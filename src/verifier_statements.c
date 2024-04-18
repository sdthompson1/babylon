/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"
#include "hash_table.h"
#include "names.h"
#include "sexpr.h"
#include "util.h"
#include "verifier.h"
#include "verifier_context.h"
#include "verifier_func.h"
#include "verifier_run.h"
#include "verifier_terms.h"
#include "verifier_types.h"
#include "verifier_statements.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void verify_var_decl_stmt(struct VContext *context,
                                 struct Statement *stmt,
                                 struct Sexpr *** ret_val_ptr)
{
    bool added_to_stack = false;

    if (stmt->var_decl.ref) {
        struct RefChain *ref = ref_chain_for_term(context, stmt->var_decl.rhs);
        hash_table_insert(context->refs, stmt->var_decl.name, ref);

    } else {
        struct Sexpr * fol_type = verify_type(stmt->var_decl.type);
        struct Sexpr * fol_rhs = verify_term(context, stmt->var_decl.rhs);

        // the rhs mustn't be allocated (unless ghost)
        if (!stmt->ghost) {
            struct Sexpr *cond = non_allocated_condition(context, stmt->var_decl.type, fol_rhs);
            if (cond) {
                verify_condition(context,
                                 stmt->var_decl.rhs->location,
                                 cond,
                                 "RHS not allocated",
                                 err_msg_assign_from_allocated(stmt->var_decl.rhs->location));
                free_sexpr(cond);
            }
        }

        update_local(context,
                     stmt->var_decl.name,
                     stmt->var_decl.type,
                     fol_type,
                     fol_rhs);

        // add it to the var decl stack - if not ghost
        if (!stmt->ghost) {
            struct NameTypeList *node = alloc(sizeof(struct NameTypeList));
            node->name = stmt->var_decl.name;
            node->type = stmt->var_decl.type;
            node->next = context->var_decl_stack;
            context->var_decl_stack = node;
            added_to_stack = true;
        }
    }

    verify_statements(context, stmt->next, ret_val_ptr);

    if (added_to_stack) {
        // the variable must be non-allocated when it goes out of scope
        char *new_name = lookup_local(context, stmt->var_decl.name);
        if (new_name) {
            if (hash_table_contains_key(context->local_env, new_name)) {
                struct Sexpr *value = make_string_sexpr_handover(new_name);
                struct Sexpr *cond = non_allocated_condition(context, stmt->var_decl.type, value);
                free_sexpr(value);

                if (cond) {
                    verify_condition(context,
                                     stmt->location,
                                     cond,
                                     "var deallocated",
                                     err_msg_var_still_allocated(stmt->var_decl.name, stmt->location));
                    free_sexpr(cond);
                }
            } else {
                free(new_name);
            }
        }

        struct NameTypeList *prev_node = context->var_decl_stack->next;
        free(context->var_decl_stack);
        context->var_decl_stack = prev_node;
    }
}

// new_expr is handed over
static void change_quantifier_to_let(struct VContext *context,
                                     struct Type *type,
                                     struct Sexpr *new_expr)
{
    // Examine the first expression in the assert list
    struct Sexpr *expr = context->assert_exprs->left;

    // Skip past any "let" expressions (from previous "fix" stmts)
    // until we find a "forall" (or "exists")
    while (expr->type == S_PAIR && expr->left->type == S_STRING
           && strcmp(expr->left->string, "let") == 0) {
        expr = expr->right->right->left;
    }

    // sanity check - expr should now be "forall" or "exists"
    if (expr->type != S_PAIR || expr->left->type != S_STRING
        || (strcmp(expr->left->string, "forall") != 0
            && strcmp(expr->left->string, "exists") != 0)) {
        fatal_error("change_quantifier_to_let: quantifier not found");
    }

    // change forall/exists to let
    free((void*)expr->left->string);
    expr->left->string = copy_string("let");

    // find the ((x TYPE)) sub-expression
    struct Sexpr *varlist = expr->right->left;
    if (get_sexpr_list_length(varlist) != 1) {
        fatal_error("change_quantifier_to_let: quantifier has wrong number of variables");
    }

    // change the "TYPE" into the new_expr
    free_sexpr(varlist->left->right->left);
    varlist->left->right->left = new_expr;

    // If there is a valid_expr, the quantifier will be followed by
    // (=> (valid-expr) stuff).
    // Delete this, if applicable (because the new_expr should already be valid!).
    struct Sexpr *vexpr = validity_test_expr(type, "");
    if (vexpr) {
        free_sexpr(vexpr);

        struct Sexpr *body = expr->right->right->left;  // body of the let
        free_sexpr(body->left);     // =>
        body->left = NULL;
        free_sexpr(body->right->left);   // valid-expr
        body->right->left = NULL;
        struct Sexpr *new_body = body->right->right->left;
        body->right->right->left = NULL;
        free_sexpr(body);

        expr->right->right->left = new_body;
    }
}

static void verify_fix_stmt(struct VContext *context, struct Statement *stmt)
{
    struct Sexpr *fol_type = verify_type(stmt->fix.type);

    struct Item *item = update_local(context,
                                     stmt->fix.name,
                                     stmt->fix.type,
                                     fol_type,
                                     NULL);

    change_quantifier_to_let(context, stmt->fix.type, make_string_sexpr(item->fol_name));
}

static void verify_obtain_stmt(struct VContext *context, struct Statement *stmt)
{
    struct Sexpr *fol_type = verify_type(stmt->obtain.type);

    // Add the item into the verifier env, without any constraints
    struct Item *item = update_local(context,
                                     stmt->obtain.name,
                                     stmt->obtain.type,
                                     fol_type,
                                     NULL);        // no initial value

    // Transform the condition
    struct Sexpr *cond = verify_term(context, stmt->obtain.condition);

    // Update the cond to say that the value must also be a valid
    // value of its type.
    struct Sexpr *var = make_string_sexpr(item->fol_name);
    cond = insert_validity_condition(context,
                                     QUANT_EXISTS,
                                     stmt->obtain.type,
                                     var,
                                     cond);

    // Verify that such a value exists.
    struct Sexpr *exists =
        make_list3_sexpr(
            make_string_sexpr("exists"),
            make_list1_sexpr(
                 make_list2_sexpr(
                     var,
                     copy_sexpr(item->fol_type))),
            copy_sexpr(cond));
    verify_condition(context, stmt->location, exists, "obtain",
                     err_msg_obtain_doesnt_exist(stmt));
    free_sexpr(exists);

    // We can now add the cond as an axiom of this item
    item->fol_axioms =
        make_pair_sexpr(
            make_list2_sexpr(
                make_string_sexpr("assert"),
                cond),
            item->fol_axioms);
}

static void verify_use_stmt(struct VContext *context, struct Statement *stmt)
{
    // Transform the given term
    struct Sexpr *witness = verify_term(context, stmt->use.term);

    // Change the goal from "exists x such-and-such" to "let
    // x=term in such-and-such".
    change_quantifier_to_let(context, stmt->use.term->type, witness);
}

static void check_assign_allocated_conditions(struct VContext *context,
                                              struct Statement *stmt,
                                              struct Sexpr *fol_rhs,   // copied/referenced
                                              struct RefChain *ref)    // copied/referenced
{
    // Ghost stmts do not require allocation checks
    if (stmt->ghost) return;

    // Check LHS is not allocated
    struct Sexpr *fol_lhs = ref_chain_to_sexpr(context, ref);
    struct Sexpr *lhs_cond = non_allocated_condition(context,
                                                     stmt->assign.lhs->type,
                                                     fol_lhs);
    if (lhs_cond) {
        verify_condition(context,
                         stmt->assign.lhs->location,
                         lhs_cond,
                         "LHS not allocated",
                         err_msg_assign_to_allocated(stmt->assign.lhs->location));
        free_sexpr(lhs_cond);
    }

    free_sexpr(fol_lhs);

    // Check RHS is not allocated
    struct Sexpr *rhs_cond = non_allocated_condition(context,
                                                     stmt->assign.rhs->type,
                                                     fol_rhs);
    if (rhs_cond) {
        verify_condition(context,
                         stmt->assign.rhs->location,
                         rhs_cond,
                         "RHS not allocated",
                         err_msg_assign_from_allocated(stmt->assign.rhs->location));
        free_sexpr(rhs_cond);
    }
}

static void verify_assign_stmt(struct VContext *context,
                               struct Statement *stmt)
{
    // Verify the RHS
    struct Sexpr *fol_rhs = verify_term(context, stmt->assign.rhs);

    // Construct reference chain for the LHS
    struct RefChain *ref = ref_chain_for_term(context, stmt->assign.lhs);

    // Check allocation conditions
    check_assign_allocated_conditions(context, stmt, fol_rhs, ref);

    // Do the assignment
    update_reference(context, ref, fol_rhs);
    fol_rhs = NULL;

    free_ref_chain(ref);
}

static void verify_swap_stmt(struct VContext *context,
                             struct Statement *stmt)
{
    struct RefChain *ref_lhs = ref_chain_for_term(context, stmt->swap.lhs);
    struct Sexpr *lhs = ref_chain_to_sexpr(context, ref_lhs);

    struct RefChain *ref_rhs = ref_chain_for_term(context, stmt->swap.rhs);
    struct Sexpr *rhs = ref_chain_to_sexpr(context, ref_rhs);

    update_reference(context, ref_lhs, rhs);
    rhs = NULL;

    update_reference(context, ref_rhs, lhs);
    lhs = NULL;

    free_ref_chain(ref_lhs);
    free_ref_chain(ref_rhs);
}

static void verify_return_stmt(struct VContext *context,
                               struct Statement *stmt,
                               struct Sexpr *** ret_val_ptr)
{
    // check that all (non-ghost) "vardecl" vars are deallocated before we return
    for (struct NameTypeList *node = context->var_decl_stack; node; node = node->next) {
        char *new_name = lookup_local(context, node->name);
        if (new_name) {
            if (hash_table_contains_key(context->local_env, new_name)) {
                struct Sexpr *value = make_string_sexpr_handover(new_name);
                struct Sexpr *cond = non_allocated_condition(context, node->type, value);
                free_sexpr(value);

                if (cond) {
                    char *sanitised = sanitise_name(node->name);
                    char *msg = copy_string_3("'", sanitised, "' deallocated");
                    free(sanitised);
                    verify_condition(context,
                                     stmt->location,
                                     cond,
                                     msg,
                                     err_msg_var_still_allocated_at_return(node->name, stmt->location));
                    free(msg);
                    free_sexpr(cond);
                }
            } else {
                free(new_name);
            }
        }
    }

    // verify the return itself (e.g. postconditions)
    verify_function_return(context,
                           stmt->location,
                           stmt->ret.value,
                           stmt->ghost,
                           ret_val_ptr);
}

static void verify_assert_stmt(struct VContext *context,
                               struct Statement *stmt)
{
    struct Sexpr *expr = verify_term(context, stmt->assert_data.condition);

    int num_facts = get_num_facts(context);

    // If there is a proof, we should "execute" it now

    // save the assert expression in the context
    context->assert_exprs = make_pair_sexpr(copy_sexpr(expr), context->assert_exprs);

    struct HashTable * hidden_backup = NULL;
    if (stmt->assert_data.proof) {
        hidden_backup = new_hash_table();
        hash_table_copy(hidden_backup, context->local_hidden);
    }

    // Execute the proof
    verify_statements(context, stmt->assert_data.proof, NULL);

    // The head of context->assert_exprs is now a modified expression to be proved
    // (where some foralls have been replaced with lets).
    // Get the SMT solver to prove the modified expression.
    verify_condition(context, stmt->location, context->assert_exprs->left, "assert",
                     err_msg_assert_failure(stmt));

    // remove the saved assert expression from the context
    struct Sexpr *tail = context->assert_exprs->right;
    free_sexpr(context->assert_exprs->left);
    free(context->assert_exprs);
    context->assert_exprs = tail;

    // Remove any intermediate facts that were established during the proof
    revert_facts(context, num_facts);

    // Add the (now proved) assert to the known facts
    add_fact(context, expr);

    if (hidden_backup) {
        free_hash_table(context->local_hidden);
        context->local_hidden = hidden_backup;
        hidden_backup = NULL;
    }
}

static void verify_assume_stmt(struct VContext *context,
                               struct Statement *stmt)
{
    struct Sexpr *expr = verify_term(context, stmt->assume.condition);

    // Just add the fact without proving it!
    add_fact(context, expr);
}

static void verify_if_stmt(struct VContext *context,
                           struct Statement *stmt,
                           struct Sexpr *** ret_val_ptr)
{
    // Verify the condition itself
    struct Sexpr *cond = verify_term(context, stmt->if_data.condition);

    struct HashTable * hidden_backup = new_hash_table();


    // Let's pretend that the condition is being assigned to a local
    // variable called "if".
    // (Because "if" is a keyword, this will not clash with any
    // source-code variable of the same name.)
    struct Item *cond_item = update_local(context,
                                          "if",
                                          NULL,
                                          make_string_sexpr("Bool"),
                                          cond);
    cond = NULL;


    // Find all vars modified on the "then" and "else" branches
    struct HashTable * modified_vars = new_hash_table();
    get_modified_vars_deref(context, modified_vars, stmt->if_data.then_block);
    get_modified_vars_deref(context, modified_vars, stmt->if_data.else_block);

    // Take a snapshot of variable versions before we start.
    struct HashTable * original_snapshot = snapshot_variable_versions(context, modified_vars);

    hash_table_copy(hidden_backup, context->local_hidden);

    // Save the original path condition
    struct Sexpr *orig_pc = context->path_condition;
    context->path_condition = NULL;


    // On the "then" branch, assume the condition is true
    // (in addition to any previous path condition)
    context->path_condition = and_sexpr(
        copy_sexpr(orig_pc),
        make_string_sexpr(cond_item->fol_name));

    // Verify the "then" branch
    verify_statements(context, stmt->if_data.then_block, ret_val_ptr);

    hash_table_copy(context->local_hidden, hidden_backup);

    // Capture new path condition from the "then" branch
    struct Sexpr *then_pc = context->path_condition;
    context->path_condition = NULL;

    // Also snapshot the variable versions from the "then" branch,
    // then revert all variables back to their "pre-if-statement" values
    struct HashTable * then_snapshot = snapshot_variable_versions(context, modified_vars);
    revert_to_snapshot(context, original_snapshot);


    // On the "else" branch, assume the condition is false
    context->path_condition = and_not_sexpr(
        orig_pc,
        make_string_sexpr(cond_item->fol_name));

    // Verify the "else" branch
    verify_statements(context, stmt->if_data.else_block, ret_val_ptr);

    free_hash_table(context->local_hidden);
    context->local_hidden = hidden_backup;
    hidden_backup = NULL;


    // Capture path condition from the "else" branch
    struct Sexpr *else_pc = context->path_condition;
    context->path_condition = NULL;


    // Propagate any changes to variables back to the parent scope.
    if (sexpr_equal_string(then_pc, "false")) {
        // We can only arrive here from the "else" branch.
        // Nothing required as the "else"-variables are already active.

    } else if (sexpr_equal_string(else_pc, "false")) {
        // We can only arrive here from the "then" branch.
        // Revert back to the "then"-variables.
        revert_to_snapshot(context, then_snapshot);

    } else {
        // Both branches are still active.
        // Resolve all vars using "ite" expressions.
        struct Sexpr *cond_var = make_string_sexpr(cond_item->fol_name);
        resolve_if_branches(context, cond_var, true, then_snapshot);
        free_sexpr(cond_var);
    }

    // Set path condition to the OR of then_pc and else_pc.
    context->path_condition = disjunction(make_list2_sexpr(then_pc, else_pc));

    free_hash_table(then_snapshot);
    free_hash_table(original_snapshot);
    free_hash_table(modified_vars);
}

static void verify_match_stmt(struct VContext *context,
                              struct Statement *stmt,
                              struct Sexpr *** ret_val_ptr)
{
    // Verify the scrutinee
    struct Sexpr *scrut = verify_term(context, stmt->match.scrutinee);

    // Find all vars modified on all arms.
    // Also add any bound vars to the environment at this point.
    struct HashTable * modified_vars = new_hash_table();
    for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {
        // Add the payload variable as a reference
        if (arm->pattern->tag == PAT_VARIANT && arm->pattern->variant.payload->tag == PAT_VAR) {
            bind_payload(context, stmt->match.scrutinee, &arm->pattern->variant);
        }

        // Now we can get the modified vars
        get_modified_vars_deref(context, modified_vars, arm->rhs);
    }

    // This snapshot will always contain the original values
    struct HashTable * original_snapshot = snapshot_variable_versions(context, modified_vars);

    // This snapshot will be updated as we process each arm
    struct HashTable * running_snapshot = snapshot_variable_versions(context, modified_vars);

    // Save the original path condition
    struct Sexpr *original_path_condition = context->path_condition;
    context->path_condition = NULL;

    struct Sexpr *captured_path_conditions = NULL;
    struct Sexpr **captured_pc_tail = &captured_path_conditions;

    struct Sexpr *all_check_exprs = NULL;
    struct Sexpr **check_expr_tail = &all_check_exprs;

    struct HashTable * hidden_backup = new_hash_table();
    hash_table_copy(hidden_backup, context->local_hidden);


    // Verify each arm
    for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {

        // Assume this pattern matches, as a path condition

        struct Sexpr *check_expr = NULL;

        if (arm->pattern->tag == PAT_VARIANT) {
            struct Type *payload_type;
            struct Sexpr *tester;
            analyse_variant(arm->pattern->variant.variant_name,
                            stmt->match.scrutinee->type,
                            &payload_type,
                            NULL,  // we don't need 'ctor'
                            &tester,
                            NULL); // we don't need 'selector'

            // The check_expr is true iff the scrutinee matches this variant
            check_expr = make_list2_sexpr(tester, copy_sexpr(scrut));

            // Assign the check_expr to a local variable, to save us repeating it
            struct Item *check_item = update_local(context,
                                                   "if",
                                                   NULL,
                                                   make_string_sexpr("Bool"),
                                                   check_expr);
            check_expr = make_string_sexpr(check_item->fol_name);

            *check_expr_tail = make_list1_sexpr(copy_sexpr(check_expr));
            check_expr_tail = &(*check_expr_tail)->right;

        } else if (arm->pattern->tag == PAT_WILDCARD) {
            check_expr = make_list2_sexpr(
                make_string_sexpr("not"),
                disjunction(all_check_exprs));
            all_check_exprs = NULL;

            struct Item *check_item = update_local(context,
                                                   "if",
                                                   NULL,
                                                   make_string_sexpr("Bool"),
                                                   check_expr);
            check_expr = make_string_sexpr(check_item->fol_name);

        } else {
            fatal_error("unexpected pattern type");
        }

        // Assume the check_expr is true
        context->path_condition =
            and_sexpr(copy_sexpr(original_path_condition),
                      copy_sexpr(check_expr));

        // Verify the right-hand-side
        verify_statements(context, arm->rhs, ret_val_ptr);

        hash_table_copy(context->local_hidden, hidden_backup);

        // Capture the new path condition
        *captured_pc_tail = make_list1_sexpr(context->path_condition);
        captured_pc_tail = &(*captured_pc_tail)->right;
        context->path_condition = NULL;

        // Resolve variables (inserting "ite" expressions where needed)
        resolve_if_branches(context, check_expr, false, running_snapshot);
        free_sexpr(check_expr);
        free_hash_table(running_snapshot);
        running_snapshot = snapshot_variable_versions(context, modified_vars);

        // Go back to the original variable values (for the next arm)
        revert_to_snapshot(context, original_snapshot);
    }

    free_hash_table(hidden_backup);
    hidden_backup = NULL;

    free_sexpr(scrut);
    free_sexpr(all_check_exprs);
    free_sexpr(original_path_condition);
    free_hash_table(original_snapshot);
    free_hash_table(modified_vars);

    // running_snapshot now contains all the correct values at the end
    // of the match
    revert_to_snapshot(context, running_snapshot);
    free_hash_table(running_snapshot);

    // Set path condition to the OR of all captured path conditions
    context->path_condition = disjunction(captured_path_conditions);
    captured_path_conditions = NULL;
}

static void verify_match_failure_stmt(struct VContext *context,
                                      struct Statement *stmt)
{
    // this should be unreachable
    struct Sexpr *condition = make_string_sexpr("false");
    verify_condition(context, stmt->location, condition, "match exhaustive",
                     err_msg_nonexhaustive_match(stmt->location));
    free_sexpr(condition);
}


// Verify that all invariants are currently true.
// Leaves path conditions and facts unchanged.
static void check_invariants(struct VContext *context,
                             struct Statement *stmt,
                             bool on_exit)
{
    int num_facts = get_num_facts(context);

    struct Attribute *attr = stmt->while_data.attributes;
    while (attr) {
        if (attr->tag == ATTR_INVARIANT) {
            struct Sexpr *expr = verify_term(context, attr->term);
            verify_condition(context, attr->term->location, expr,
                             on_exit ? "invariant at exit" : "invariant at entry",
                             on_exit ? err_msg_invariant_violated_on_exit(attr)
                                     : err_msg_invariant_violated_on_entry(attr));

            // Add the invariant as a fact for the next invariant
            add_fact(context, expr);
        }

        attr = attr->next;
    }

    // Remove any added facts
    revert_facts(context, num_facts);
}

// Get current value of the variant.
static struct Sexpr * get_variant_value(struct VContext *context,
                                        struct Statement *stmt)
{
    struct Attribute *attr = stmt->while_data.attributes;
    while (attr) {
        if (attr->tag == ATTR_DECREASES) {
            return verify_term(context, attr->term);
        }
        attr = attr->next;
    }
    fatal_error("no decreases attribute");
}

// Give all the modified variables new FOL-names, using declare-const so the solver
// doesn't know anything about their value.
// Also add all invariants as facts (given current path condition).
static void havoc_variables(struct VContext *context,
                            struct HashTable *modified_vars,
                            struct Statement *stmt)
{
    // "Havoc" each modified variable
    struct HashIterator *iter = new_hash_iterator(modified_vars);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct Type *type = value;
        struct Sexpr *fol_type = verify_type(type);
        update_local(context, key, type, fol_type, NULL);
    }
    free_hash_iterator(iter);

    // Re-assert the invariants
    struct Attribute *attr = stmt->while_data.attributes;
    while (attr) {
        if (attr->tag == ATTR_INVARIANT) {
            struct Sexpr *expr = verify_term(context, attr->term);
            add_fact(context, expr);
        }
        attr = attr->next;
    }
}

// Return a "<" expression comparing variant terms
static struct Sexpr * variant_cmp_expr(struct Type *type,
                                       struct Sexpr *old_variant,   // handover
                                       struct Sexpr *new_variant)   // handover
{
    switch (type->tag) {
    case TY_BOOL:
        // new_variant must be false and old_variant must be true, for a decrease
        return make_list3_sexpr(
            make_string_sexpr("and"),
            old_variant,
            make_list2_sexpr(make_string_sexpr("not"), new_variant));

    case TY_FINITE_INT:
    case TY_MATH_INT:
        // new_variant must be strictly less than old
        return make_list3_sexpr(
            make_string_sexpr("<"),
            new_variant,
            old_variant);

    case TY_RECORD:
        if (type->record_data.fields == NULL) {
            free_sexpr(old_variant);
            free_sexpr(new_variant);
            return make_string_sexpr("false");

        } else {
            struct Sexpr *rec_type = verify_type(type);

            struct Sexpr *cmp_expr = NULL;
            struct Sexpr **cmp_tail = &cmp_expr;

            struct Sexpr *old_list = NULL;
            struct Sexpr **old_tail = &old_list;

            struct Sexpr *new_list = NULL;
            struct Sexpr **new_tail = &new_list;

            uint32_t n = 0;
            for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
                char num[30];
                sprintf(num, "%" PRIu32, n);
                ++n;

                struct Sexpr *old_var = make_string_sexpr_handover(copy_string_2("$old", num));
                struct Sexpr *new_var = make_string_sexpr_handover(copy_string_2("$new", num));

                *old_tail = make_list1_sexpr(copy_sexpr(old_var));
                old_tail = &(*old_tail)->right;

                *new_tail = make_list1_sexpr(copy_sexpr(new_var));
                new_tail = &(*new_tail)->right;

                if (field->next == NULL) {
                    *cmp_tail = variant_cmp_expr(field->type, old_var, new_var);

                } else {
                    struct Sexpr *inner_expr =
                        make_list3_sexpr(
                            make_string_sexpr("and"),
                            make_list3_sexpr(make_string_sexpr("="),
                                             copy_sexpr(old_var),
                                             copy_sexpr(new_var)),
                            NULL);

                    *cmp_tail =
                        make_list3_sexpr(
                            make_string_sexpr("or"),
                            variant_cmp_expr(field->type, old_var, new_var),
                            inner_expr);

                    cmp_tail = &(*cmp_tail)->right->right->left->right->right->left;
                }
            }

            struct Sexpr *inner_match =
                make_list3_sexpr(
                    make_string_sexpr("match"),
                    new_variant,
                    make_list1_sexpr(
                        make_list2_sexpr(
                            make_pair_sexpr(copy_sexpr(rec_type), new_list),
                            cmp_expr)));

            return make_list3_sexpr(
                       make_string_sexpr("match"),
                       old_variant,
                       make_list1_sexpr(
                           make_list2_sexpr(
                               make_pair_sexpr(rec_type, old_list),
                               inner_match)));
        }

    case TY_VAR:
    case TY_VARIANT:
    case TY_ARRAY:
    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
    case TY_APP:
    case TY_MATH_REAL:
        // the typechecker shouldn't allow these as 'decreases' expressions
        fatal_error("decreases clause - unexpected type");
    }

    fatal_error("decreases clause - unhandled case");
}

static struct Sexpr *variant_bounded_expr(struct Type *type,
                                          struct Sexpr *variant)
{
    switch (type->tag) {
    case TY_BOOL:
    case TY_FINITE_INT:
        return NULL;

    case TY_MATH_INT:
        return make_list3_sexpr(make_string_sexpr(">="),
                                copy_sexpr(variant),
                                make_string_sexpr("0"));

    case TY_RECORD:
        ;

        // first get the list of field types, so we can do $FLD projections
        struct Sexpr *field_types = NULL;
        struct Sexpr **field_types_tail = &field_types;
        for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
            *field_types_tail = make_list1_sexpr(verify_type(field->type));
            field_types_tail = &(*field_types_tail)->right;
        }

        // make a list of boundedness conditions
        struct Sexpr *cond_list = NULL;
        struct Sexpr **cond_tail = &cond_list;

        // iterate through the fields
        uint32_t num = 0;
        for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {

            // project out this field
            char fld[30];
            sprintf(fld, "$FLD%" PRIu32, num);

            struct Sexpr *field_proj_sexpr = make_string_sexpr(fld);
            make_instance(&field_proj_sexpr, copy_sexpr(field_types));

            field_proj_sexpr = make_list2_sexpr(field_proj_sexpr, copy_sexpr(variant));

            // figure out the condition for this field to be bounded (if any)
            struct Sexpr *field_bound_cond = variant_bounded_expr(field->type, field_proj_sexpr);

            free_sexpr(field_proj_sexpr);
            field_proj_sexpr = NULL;

            if (field_bound_cond) {
                // add it to the list
                *cond_tail = make_list1_sexpr(field_bound_cond);
                cond_tail = &(*cond_tail)->right;
            }

            ++num;
        }

        // field_types no longer needed
        free_sexpr(field_types);
        field_types = NULL;

        // return the conjunction of all conditions (if any)
        if (cond_list) {
            return conjunction(cond_list);
        } else {
            return NULL;
        }

    case TY_VAR:
    case TY_VARIANT:
    case TY_ARRAY:
    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
    case TY_APP:
    case TY_MATH_REAL:
        // the typechecker shouldn't allow these as 'decreases' expressions
        fatal_error("decreases clause - unexpected type");
    }

    fatal_error("decreases clause - unhandled case");
}

// Verify that the new variant is lower than the old.
// May modify the path condition.
static void check_variant_has_decreased(struct VContext *context,
                                        struct Statement *while_stmt,
                                        struct Sexpr *old_variant,
                                        struct Sexpr *new_variant)
{
    struct Attribute *attr = while_stmt->while_data.attributes;
    while (attr) {
        if (attr->tag == ATTR_DECREASES) {
            break;
        }
        attr = attr->next;
    }

    // Assert that the loop-condition is still true.
    struct Sexpr *expr = verify_term(context, while_stmt->while_data.condition);
    context->path_condition = and_sexpr(context->path_condition, expr);

    // Compare the variants.
    struct Sexpr *cmp_expr = variant_cmp_expr(attr->term->type,
                                              copy_sexpr(old_variant), copy_sexpr(new_variant));
    verify_condition(context, attr->location, cmp_expr, "decreases",
                     err_msg_decreases_might_not_decrease(attr));
    free_sexpr(cmp_expr);
}

// Verify that the variant is bounded below - this is automatic for TY_FINITE_INT and TY_BOOL
// but needs to be checked for TY_MATH_INT.
static void check_variant_is_bounded(struct VContext *context,
                                     struct Statement *while_stmt,
                                     struct Sexpr *variant)
{
    struct Attribute *attr = while_stmt->while_data.attributes;
    while (attr) {
        if (attr->tag == ATTR_DECREASES) {
            break;
        }
        attr = attr->next;
    }

    struct Sexpr *bounded_expr = variant_bounded_expr(attr->term->type,
                                                      variant);
    if (bounded_expr) {
        verify_condition(context, attr->location, bounded_expr, "decreases bounded below",
                         err_msg_decreases_not_bounded_below(attr));
        free_sexpr(bounded_expr);
    }
}

void verify_while_stmt(struct VContext *context,
                       struct Statement *stmt,
                       struct Sexpr *** ret_val_ptr)
{
    // Verify that the invariants hold on entry.
    check_invariants(context, stmt, false);


    // Find the variables modified in the loop.
    struct HashTable *modified_vars = new_hash_table();
    get_modified_vars_deref(context, modified_vars, stmt->while_data.body);


    // Reset all variables modified in the while loop to indeterminate values.
    // Also add facts to say that the invariants remain satisfied.
    havoc_variables(context, modified_vars, stmt);


    // We want to keep these new facts, but we will be removing any facts
    // generated during the while-loop itself
    int num_facts = get_num_facts(context);


    // Assign the loop-condition to a special variable named "while".
    // (Because "while" is a keyword, we can be sure there is no source-code
    // variable named "while".)
    struct Sexpr *cond_expr = verify_term(context, stmt->while_data.condition);
    struct Item *cond_item = update_local(context,
                                          "while",
                                          NULL,
                                          make_string_sexpr("Bool"),
                                          cond_expr);
    cond_expr = NULL;

    // Add a path condition that the loop-condition is true.
    struct Sexpr *path_cond_before = context->path_condition;
    context->path_condition = and_sexpr(copy_sexpr(path_cond_before),
                                        make_string_sexpr(cond_item->fol_name));

    // Snapshot the current version numbers of each variable (as we will
    // need to reset back again after the loop)
    struct HashTable *snapshot = snapshot_variable_versions(context, modified_vars);
    free_hash_table(modified_vars);
    modified_vars = NULL;

    // Get variant at start of loop
    struct Sexpr *initial_variant = get_variant_value(context, stmt);

    // Verify that the initial variant is bounded
    check_variant_is_bounded(context, stmt, initial_variant);

    struct HashTable *hidden_backup = new_hash_table();
    hash_table_copy(hidden_backup, context->local_hidden);

    // Verify the loop body
    verify_statements(context, stmt->while_data.body, ret_val_ptr);

    // Verify that the invariant still holds
    check_invariants(context, stmt, true);

    // Verify that the variant has decreased
    struct Sexpr *new_variant = get_variant_value(context, stmt);
    check_variant_has_decreased(context, stmt, initial_variant, new_variant);
    free_sexpr(new_variant);

    free_sexpr(initial_variant);
    initial_variant = NULL;


    // Now consider instead the case where the loop condition is false.
    free_sexpr(context->path_condition);
    context->path_condition = and_not_sexpr(path_cond_before,
                                            make_string_sexpr(cond_item->fol_name));
    path_cond_before = NULL;

    revert_to_snapshot(context, snapshot);
    free_hash_table(snapshot);
    snapshot = NULL;

    free_hash_table(context->local_hidden);
    context->local_hidden = hidden_backup;
    hidden_backup = NULL;

    // Remove any facts that were derived during the loop (since we
    // are now considering the case where the loop condition is false
    // and the loop doesn't run).
    revert_facts(context, num_facts);
}


static void verify_call_stmt(struct VContext *context, struct Statement *stmt)
{
    struct Sexpr *fol_call_term = verify_call_term(context, stmt->call.term);
    free_sexpr(fol_call_term);
}

static void verify_show_hide_stmt(struct VContext *context, struct Statement *stmt)
{
    if (stmt->show_hide.show) {
        hash_table_remove(context->local_hidden, stmt->show_hide.name);
    } else {
        hash_table_insert(context->local_hidden, stmt->show_hide.name, NULL);
    }
}


void verify_statements(struct VContext *context,
                       struct Statement *stmt,
                       struct Sexpr *** ret_val_ptr)
{
    while (stmt) {
        if (context->error_found && !fol_continue_after_error()) {
            // We might as well stop here
            return;
        }

        switch (stmt->tag) {
        case ST_VAR_DECL:
            // verify_var_decl_stmt will itself do the rest of the list
            verify_var_decl_stmt(context, stmt, ret_val_ptr);
            return;

        case ST_FIX:
            verify_fix_stmt(context, stmt);
            break;

        case ST_OBTAIN:
            verify_obtain_stmt(context, stmt);
            break;

        case ST_USE:
            verify_use_stmt(context, stmt);
            break;

        case ST_ASSIGN:
            verify_assign_stmt(context, stmt);
            break;

        case ST_SWAP:
            verify_swap_stmt(context, stmt);
            break;

        case ST_RETURN:
            verify_return_stmt(context, stmt, ret_val_ptr);
            break;

        case ST_ASSERT:
            verify_assert_stmt(context, stmt);
            break;

        case ST_ASSUME:
            verify_assume_stmt(context, stmt);
            break;

        case ST_IF:
            verify_if_stmt(context, stmt, ret_val_ptr);
            break;

        case ST_WHILE:
            verify_while_stmt(context, stmt, ret_val_ptr);
            break;

        case ST_CALL:
            verify_call_stmt(context, stmt);
            break;

        case ST_MATCH:
            verify_match_stmt(context, stmt, ret_val_ptr);
            break;

        case ST_MATCH_FAILURE:
            verify_match_failure_stmt(context, stmt);
            break;

        case ST_SHOW_HIDE:
            verify_show_hide_stmt(context, stmt);
            break;
        }

        stmt = stmt->next;
    }
}
