/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "cache_db.h"
#include "error.h"
#include "hash_table.h"
#include "sexpr.h"
#include "stacked_hash_table.h"
#include "util.h"
#include "verifier.h"
#include "verifier_context.h"
#include "verifier_decls.h"
#include "verifier_func.h"
#include "verifier_run.h"
#include "verifier_terms.h"
#include "verifier_types.h"
#include "verifier_statements.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void verify_const_decl(struct VContext *context,
                              const char *name,
                              struct DeclData_Const *data,
                              const uint8_t fingerprint[SHA256_HASH_LENGTH])
{
    char *fol_name = copy_string_2("%", name);
    struct Sexpr *fol_type = verify_type(data->type);
    struct Sexpr *fol_term = NULL;

    if (data->rhs) {
        if (data->value) {
            // Set fol_term from data->value (which is the original rhs
            // reduced to normal form).
            // We use this, rather than data->rhs, for two reasons:
            // (1) Optimisation: the normal form is usually shorter and
            //     easier for the solver to deal with.
            // (2) Correctness: some term types (record-updates in
            //     particular) rely on inserting special symbols (like
            //     "$RecordUpdate") into the local env. This wouldn't work
            //     for a global const decl. These terms do not occur in
            //     normal forms, so using the normal form will be safe.
            fol_term = verify_term(context, data->value);
        } else {
            // This is probably a ghost decl, where the rhs doesn't need
            // to be evaluated to normal form.
            // In this case, the RHS might fail to verify. That's fine, we
            // just report the verification error and continue.
            fol_term = verify_term(context, data->rhs);
        }
    }

    struct Item *item = add_const_item(context, fol_name, data->type, fol_type, fol_term, false);
    memcpy(item->fingerprint, fingerprint, SHA256_HASH_LENGTH);
}

static void prepare_args(struct VContext *context,
                         struct FunArg *arg,
                         struct Sexpr ** type_list,
                         struct Sexpr ** name_type_list,
                         struct Sexpr ** name_list)
{
    *type_list = *name_type_list = *name_list = NULL;

    while (arg) {
        struct Sexpr * type = verify_type(arg->type);

        // Add this arg to the context as a local variable
        struct Item *item = update_local(context, arg->name,
                                         arg->type, copy_sexpr(type), NULL);

        // Extend the various lists
        struct Sexpr * type_node = make_list1_sexpr(copy_sexpr(type));

        struct Sexpr * name_type_node = make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr(item->fol_name),
                type));
        type = NULL;

        struct Sexpr * name_node = make_list1_sexpr(make_string_sexpr(item->fol_name));

        *type_list = type_node;
        type_list = &type_node->right;

        *name_type_list = name_type_node;
        name_type_list = &name_type_node->right;

        *name_list = name_node;
        name_list = &name_node->right;

        arg = arg->next;
    }
}

static void verify_function_attributes(struct VContext *context,
                                       struct Location location,
                                       struct Attribute *attr,
                                       struct Type *ret_type,
                                       bool need_alloc_check,
                                       struct Condition ***precond_tail,
                                       struct Condition ***postcond_tail)
{
    int num_facts_after_requires = get_num_facts(context);

    while (attr) {
        switch (attr->tag) {
        case ATTR_REQUIRES:
        case ATTR_ENSURES:
            {
                struct Sexpr *cond = verify_term(context, attr->term);

                // We can assume the condition while validating
                // the rest of the attributes
                add_fact(context, copy_sexpr(cond));

                // We want to keep preconditions "permanently"
                if (attr->tag == ATTR_REQUIRES) {
                    num_facts_after_requires = get_num_facts(context);
                }

                // Insert lets so that we can use the condition "externally"
                cond = insert_lets(context, cond);

                // Save the condition to the appropriate list
                if (cond) {
                    struct Condition ***tail_ptr =
                        attr->tag == ATTR_REQUIRES ? precond_tail : postcond_tail;
                    struct Condition *node = alloc(sizeof(struct Condition));
                    node->location = attr->location;
                    node->expr = cond;
                    node->next = NULL;
                    **tail_ptr = node;
                    *tail_ptr = &node->next;
                } else {
                    // this is unexpected, since pre/post
                    // conditions do not have any "while" stmts or
                    // similar constructs that would cause
                    // insert_lets to fail.
                    fatal_error("failed to add lets to pre/postcondition");
                }
            }
            break;

        case ATTR_INVARIANT:
        case ATTR_DECREASES:
            fatal_error("unexpected function attribute");
        }

        attr = attr->next;
    }

    // If need_alloc_check (currently true for 'extern' functions) and
    // the function returns a value, then we verify that the return
    // value is not allocated (given the preconditions and
    // postconditions).
    if (need_alloc_check && ret_type) {
        struct Sexpr *is_alloc = allocated_test_expr(context, ret_type, "%return");
        if (is_alloc != NULL) {  // NULL means it is never allocated
            struct Sexpr *is_not_alloc = make_list2_sexpr(make_string_sexpr("not"), is_alloc);
            verify_condition(context,
                             location,
                             is_not_alloc,
                             "return value not allocated",
                             err_msg_return_allocated(location));
            free_sexpr(is_not_alloc);
        }
    }

    // remove the postconditions afterwards (but not the preconditions)
    revert_facts(context, num_facts_after_requires);
}

static struct Sexpr *make_and_sexpr(struct Condition *cond)
{
    // cond should be non-NULL
    if (cond->next == NULL) {
        return copy_sexpr(cond->expr);
    } else {
        struct Sexpr *result = make_list1_sexpr(make_string_sexpr("and"));
        struct Sexpr **next_ptr = &result->right;
        while (cond) {
            *next_ptr = make_list1_sexpr(copy_sexpr(cond->expr));
            next_ptr = &((*next_ptr)->right);
            cond = cond->next;
        }
        return result;
    }
}

static struct Sexpr * apply_theta(struct Sexpr *theta, struct Condition *conditions)
{
    struct Sexpr *sexpr = make_and_sexpr(conditions);
    if (theta) {
        sexpr = make_list3_sexpr(make_string_sexpr("let"),
                                 copy_sexpr(theta),
                                 sexpr);
    }
    return sexpr;
}

static void check_implies(struct VContext *context,
                          struct Location loc,
                          struct Sexpr *theta_premises_1,
                          struct Condition *premises_1,
                          struct Sexpr *theta_premises_2,
                          struct Condition *premises_2,
                          struct Sexpr *theta_conclusions,
                          struct Condition *conclusions,
                          const char *err_msg)  // handover
{
    if (!conclusions) {
        // there is nothing to check
        free((char*)err_msg);
        return;
    }

    struct Sexpr * sexpr = apply_theta(theta_conclusions, conclusions);

    if (premises_2) {
        sexpr = make_list3_sexpr(make_string_sexpr("=>"),
                                 apply_theta(theta_premises_2, premises_2),
                                 sexpr);
    }

    if (premises_1) {
        sexpr = make_list3_sexpr(make_string_sexpr("=>"),
                                 apply_theta(theta_premises_1, premises_1),
                                 sexpr);
    }

    verify_condition(context, loc, sexpr, "interface consistency", err_msg);
    err_msg = NULL;
    free_sexpr(sexpr);
}

static struct Sexpr * make_generic_fun_params(const struct TyVarList *tyvars)
{
    struct Sexpr *list = NULL;
    struct Sexpr **tail = &list;
    while (tyvars) {
        // Each type variable expands into four generic params:
        //  - the type itself
        //  - a default value of that type
        //  - a function telling whether a value of the type is "allocated" or not
        //  - a function telling whether a value of the type is valid or not.
        *tail = make_list1_sexpr(make_string_sexpr_handover(copy_string_2("%", tyvars->name)));
        tail = &((*tail)->right);

        *tail = make_list1_sexpr(make_string_sexpr_handover(copy_string_2("$default-%", tyvars->name)));
        tail = &((*tail)->right);

        *tail = make_list1_sexpr(make_string_sexpr_handover(copy_string_2("$allocated-%", tyvars->name)));
        tail = &((*tail)->right);

        *tail = make_list1_sexpr(make_string_sexpr_handover(copy_string_2("$valid-%", tyvars->name)));
        tail = &((*tail)->right);

        tyvars = tyvars->next;
    }
    return list;
}

static void make_generic(struct Sexpr **expr,
                         const char *name,
                         struct Sexpr *tyvar_list)
{
    if (*expr && tyvar_list != NULL) {
        *expr = make_list4_sexpr(make_string_sexpr("generic"),
                                 make_string_sexpr(name),
                                 copy_sexpr(tyvar_list),
                                 *expr);
    }
}

static void make_generic_list(struct Sexpr *expr,
                              const char *name,
                              struct Sexpr *tyvar_list)
{
    while (expr) {
        make_generic(&expr->left, name, tyvar_list);
        expr = expr->right;
    }
}

static struct HashTable *make_new_values(struct FunArg *args, struct Sexpr *fol_ret_type)
{
    struct HashTable *table = new_hash_table();

    bool ref_found = false;
    int n = 1;
    for (; args; args = args->next) {
        if (args->ref) {
            struct Sexpr *expr = make_list2_sexpr(
                ret_fldn(n, fol_ret_type),
                make_string_sexpr("%return"));
            hash_table_insert(table, args->name, expr);
            ref_found = true;
            ++n;
        }
    }

    struct Sexpr *ret = make_string_sexpr("%return");
    if (ref_found) {
        ret = make_list2_sexpr(ret_fldn(0, fol_ret_type), ret);
    }
    hash_table_insert(table, "return", ret);

    return table;
}

static void ht_free_sexpr(void *context, const char *key, void *value)
{
    free_sexpr(value);
}

// Given "postcond", returns
// (assert (forall (ARGS) (let ((%return (%f ARGS))) (=> (VALID args) (=> preconditions postcond)))))
// "postcond" is handed over. "name_type_list" is copied.
static struct Sexpr * make_postcond_assert(struct VContext *context,
                                           struct Sexpr *name_type_list,
                                           struct Condition *preconds,
                                           struct Sexpr *postcond)
{
    for (struct Condition *cond = preconds; cond; cond = cond->next) {
        postcond = make_list3_sexpr(make_string_sexpr("=>"),
                                    copy_sexpr(cond->expr),
                                    postcond);
    }

    // (=> (VALID args) postcond)
    postcond = insert_validity_conditions(context,
                                          QUANT_FORALL,
                                          context->function_args,
                                          context->funapp_sexpr,
                                          postcond);

    // (let ((%return (%f ARGS))) ...)
    postcond = add_return_if_required(copy_sexpr(context->funapp_sexpr), postcond);

    // (assert (forall (ARGS) ...))
    if (name_type_list != NULL) {
        postcond = make_list3_sexpr(
            make_string_sexpr("forall"),
            copy_sexpr(name_type_list),
            postcond);
    }
    postcond = make_list2_sexpr(make_string_sexpr("assert"), postcond);

    return postcond;
}

static struct Sexpr * make_fol_dummy_subst(struct Item *from, struct Item *to)
{
    struct Sexpr *result = NULL;
    struct Sexpr **result_tail = &result;

    struct Sexpr *from_dummy = from->fol_dummies;
    struct Sexpr *to_dummy = to->fol_dummies;
    while (from_dummy && to_dummy) {
        if (strcmp(from_dummy->left->string, to_dummy->left->string) != 0) {
            *result_tail = make_list1_sexpr(
                               make_list2_sexpr(
                                   copy_sexpr(from_dummy->left),
                                   copy_sexpr(to_dummy->left)));
            result_tail = &(*result_tail)->right;
        }
        from_dummy = from_dummy->right;
        to_dummy = to_dummy->right;
    }
    if (from_dummy || to_dummy) {
        fatal_error("make_fol_dummy_subst: different length lists");
    }

    return result;
}

static void verify_function_decl(struct VContext *context,
                                 struct Decl *decl,
                                 const uint8_t fingerprint[SHA256_HASH_LENGTH])
{
    // First let's see if there is an existing (interface) definition for this function
    char *fol_name = copy_string_2("%", decl->name);
    struct Item *interface_item = stacked_hash_table_lookup(context->stack, fol_name);

    struct DeclData_Function *data = &decl->function_data;


    // Add tyvars to the env
    add_tyvars_to_env(context, data->tyvars);

    // Process the args, add them to env
    struct Sexpr *type_list;
    struct Sexpr *name_type_list;
    struct Sexpr *name_list;
    prepare_args(context, data->args, &type_list, &name_type_list, &name_list);
    context->function_args = decl->function_data.args;
    context->arglist_sexpr = name_type_list;


    // Figure out the fake return-type of the function (including any updated ref values)
    struct Type *fake_ret_type = get_expanded_ret_type(data->args, data->return_type);
    struct Sexpr *fol_fake_ret_type = verify_type(fake_ret_type);

    // Add %return to the env
    add_const_item(context,
                   copy_string("%return"),
                   fake_ret_type,
                   copy_sexpr(fol_fake_ret_type),
                   NULL,
                   true);

    // Setup the hashtable for translating "new" versions of the ref args.
    context->new_values = make_new_values(data->args, fol_fake_ret_type);

    // Make an Item to represent the function
    struct Item *item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));

    // (declare-fun name type_list ret_type)
    // (Not needed for impure functions!)
    if (!decl->function_data.impure) {
        item->fol_decl = make_list4_sexpr(make_string_sexpr("declare-fun"),
                                          make_string_sexpr(fol_name),
                                          type_list,
                                          copy_sexpr(fol_fake_ret_type));
    } else {
        free_sexpr(type_list);
    }
    type_list = NULL;

    item->fol_axioms = NULL;
    item->fol_name = copy_string(fol_name);
    item->fol_type = NULL;

    item->fol_generic_vars = make_generic_fun_params(data->tyvars);

    // Verify the preconds/postconds, and add the preconds to the list of known facts
    struct Condition *preconds = NULL;
    struct Condition **precond_tail = &preconds;
    struct Condition *postconds = NULL;
    struct Condition **postcond_tail = &postconds;
    verify_function_attributes(context,
                               decl->location,
                               decl->attributes,
                               data->return_type,
                               data->is_extern, // need_alloc_check
                               &precond_tail,
                               &postcond_tail);

    // set funapp_sexpr to (%f %x %y)
    // (or just %f if no args)
    // (Not needed for impure functions)
    if (!data->impure) {
        if (name_list == NULL) {
            context->funapp_sexpr = make_string_sexpr(fol_name);
        } else {
            context->funapp_sexpr =
                make_pair_sexpr(make_string_sexpr(fol_name), copy_sexpr(name_list));
        }
    }

    if (data->body_specified) {
        context->postconds = postconds;

        struct Sexpr *fun_defn_expr = NULL;
        struct Sexpr **fun_defn_tail = &fun_defn_expr;
        verify_statements(context, data->body, &fun_defn_tail);

        if (context->var_decl_stack != NULL) {
            fatal_error("var decl stack not empty");
        }

        if (data->return_type) {
            // End of non-void function
            // Verify that this is unreachable code
            struct Sexpr *false_expr = make_string_sexpr("false");
            verify_condition(context,
                             data->end_loc,
                             false_expr,
                             "end of function unreachable",
                             err_msg_end_of_function_reached(data->end_loc));
            free_sexpr(false_expr);
        } else {
            // End of void function
            // Verify that the postconditions hold
            verify_function_return(context, data->end_loc,
                                   NULL, decl->ghost, &fun_defn_tail);
        }

        context->postconds = NULL;

        // If we got a fun_defn_expr then let's change our declare-fun into
        // a define-fun.
        if (fun_defn_expr != NULL && !data->impure) {
            if (*fun_defn_tail == NULL) {
                struct Sexpr *arbitrary = make_string_sexpr("$ARBITRARY");
                make_instance(&arbitrary, make_list1_sexpr(copy_sexpr(fol_fake_ret_type)));
                *fun_defn_tail = arbitrary;
            }
            fun_defn_expr = insert_lets(context, fun_defn_expr);
            if (fun_defn_expr != NULL) {
                // (define-fun name name_type_list type expr)
                free_sexpr(item->fol_decl->left);
                item->fol_decl->left = make_string_sexpr("define-fun");
                free_sexpr(item->fol_decl->right->right->left);
                item->fol_decl->right->right->left = copy_sexpr(name_type_list);
                item->fol_decl->right->right->right->right = make_list1_sexpr(fun_defn_expr);
                fun_defn_expr = NULL;
            }
        } else if (fun_defn_expr != NULL) {
            // Impure function - the translated body is not needed - discard it.
            free_sexpr(fun_defn_expr);
            fun_defn_expr = NULL;
        }
    }

    if (!data->impure) {
        // Add an axiom to say that the return-value(s) are valid,
        // given that the input-value(s) are valid for their types,
        // and the preconditions hold.
        struct Sexpr **tail_ptr = &item->fol_axioms;
        struct Sexpr *ret_validity = ret_validity_test(data->args, data->return_type, fol_fake_ret_type);
        if (ret_validity) {
            ret_validity = make_postcond_assert(context,
                                                name_type_list,
                                                preconds,
                                                ret_validity);
            *tail_ptr = make_list1_sexpr(ret_validity);
            tail_ptr = &((*tail_ptr)->right);
        }

        // Add the postconditions as additional axioms
        // (again, under appropriate assumptions on the input).
        for (struct Condition *cond = postconds; cond; cond = cond->next) {
            struct Sexpr *expr = copy_sexpr(cond->expr);

            expr = make_postcond_assert(context,
                                        name_type_list,
                                        preconds,
                                        expr);

            *tail_ptr = make_list1_sexpr(expr);
            tail_ptr = &((*tail_ptr)->right);
        }

        // Make the fol_decl and fol_axioms generic if required
        make_generic(&item->fol_decl, item->fol_name, item->fol_generic_vars);
        make_generic_list(item->fol_axioms, item->fol_name, item->fol_generic_vars);
    }

    // Save pre/post conditions to the Item
    item->fol_dummies = name_list;
    name_list = NULL;

    item->preconds = preconds;
    preconds = NULL;

    item->postconds = postconds;
    postconds = NULL;

    memcpy(item->fingerprint, fingerprint, SHA256_HASH_LENGTH);

    // Free things
    free_sexpr(name_type_list);
    name_type_list = NULL;

    free_sexpr(context->funapp_sexpr);
    context->funapp_sexpr = NULL;
    context->function_args = NULL;  // this was shared with the Decl so shouldn't be freed
    context->arglist_sexpr = NULL;

    hash_table_for_each(context->new_values, ht_free_sexpr, NULL);
    free_hash_table(context->new_values);
    context->new_values = NULL;

    free_type(fake_ret_type);
    fake_ret_type = NULL;
    free_sexpr(fol_fake_ret_type);
    fol_fake_ret_type = NULL;

    // Reset path condition and facts...
    free_sexpr(context->path_condition);
    context->path_condition = make_string_sexpr("true");
    revert_facts(context, 0);

    // Confirm that the preconds and postconds are consistent with the interface (if applicable)
    if (interface_item) {
        struct Sexpr *theta = make_fol_dummy_subst(interface_item, item);
        check_implies(context,
                      decl->location,
                      theta, interface_item->preconds,
                      NULL, NULL,
                      NULL, item->preconds,
                      err_msg_inconsistent_preconds(decl));
        check_implies(context,
                      decl->location,
                      theta, interface_item->preconds,
                      NULL, item->postconds,
                      theta, interface_item->postconds,
                      err_msg_inconsistent_postconds(decl));
        free_sexpr(theta);
    }

    // Done, add Item to the env.
    remove_existing_item(context->stack->base->table, fol_name);   // remove from global env
    hash_table_insert(context->stack->base->table, fol_name, item);   // add to global env
}

static void remove_previous_abstract_type(struct VContext *context,
                                          const char *name)
{
    char *fol_name = copy_string_2("%", name);
    remove_existing_item(context->stack->base->table, fol_name);

    char *default_name = copy_string_2("$default-", fol_name);
    remove_existing_item(context->stack->base->table, default_name);
    free(default_name);

    char *allocated_name = copy_string_2("$allocated-", fol_name);
    remove_existing_item(context->stack->base->table, allocated_name);
    free(allocated_name);

    char *valid_name = copy_string_2("$valid-", fol_name);
    remove_existing_item(context->stack->base->table, valid_name);
    free(valid_name);

    free(fol_name);
}

static void verify_typedef_decl(struct VContext *context,
                                struct Decl *decl,
                                const uint8_t fingerprint[SHA256_HASH_LENGTH])
{
    remove_previous_abstract_type(context, decl->name);

    struct Item *item;

    if (decl->typedef_data.rhs == NULL) {

        // We are declaring a new abstract type (e.g. "type Foo;" or "extern type Foo;").
        // We need to add a "proper" Item in this case.

        item = add_tyvar_to_env(context, decl->name, false, decl->typedef_data.alloc_level);

    } else {
        // We are declaring a typedef (e.g. "type Foo = i32;").
        // In this case, the typechecker will already have substituted out the
        // typedef, so the verifier won't ever use the Item that we create here.
        // So it can be a fake Item with most fields equal to zero.
        // We do still need to fill in the fingerprint field though (recall that
        // the fingerprints are used when checking decl->dependency_names, and
        // decl->dependency_names is created pre-typechecking, so it might still
        // contain references to typedef-names!).
        item = alloc(sizeof(struct Item));
        memset(item, 0, sizeof(struct Item));
        char *fol_name = copy_string_2("%", decl->name);
        hash_table_insert(context->stack->base->table, fol_name, item);  // add to global env
    }

    memcpy(item->fingerprint, fingerprint, SHA256_HASH_LENGTH);
}

static void verify_datatype_decl(struct VContext *context,
                                 struct Decl *decl,
                                 const uint8_t fingerprint[SHA256_HASH_LENGTH])
{
    remove_previous_abstract_type(context, decl->name);

    // Datatype Items aren't directly used, although we still need one
    // to hold the fingerprint.
    struct Item *item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));
    memcpy(item->fingerprint, fingerprint, SHA256_HASH_LENGTH);

    char *fol_name = copy_string_2("%", decl->name);
    hash_table_insert(context->stack->base->table, fol_name, item);  // add to global env

    // Also insert fake Items for the data ctors. These are again only used
    // for fingerprinting.
    for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
        item = alloc(sizeof(struct Item));
        memset(item, 0, sizeof(struct Item));
        memcpy(item->fingerprint, fingerprint, SHA256_HASH_LENGTH);

        char *fol_name = copy_string_2("%", ctor->name);
        hash_table_insert(context->stack->base->table, fol_name, item);  // add to global env
    }
}

static void free_string_names_entry(void *context, const char *key, void *value)
{
    if (strcmp(key, "$DefaultArrayNum") != 0 && strcmp(key, "$ArrayLiteralNum") != 0) {
        free((char*)key);
        free_term(value);
    }
}

static void clear_string_names_hash_table(struct HashTable *string_names)
{
    hash_table_for_each(string_names, free_string_names_entry, NULL);
    hash_table_clear(string_names);
}

// Lookup the fingerprint of an existing (global) Decl.
// Returns NULL if not found.
static const uint8_t * lookup_decl_fingerprint(struct StackedHashTable *global_env,
                                               const char *name)
{
    char *fol_name = copy_string_2("%", name);
    struct Item *item = stacked_hash_table_lookup(global_env, fol_name);
    free(fol_name);

    if (item) {
        // Sanity check: the fingerprint should not be all zeroes.
        bool found_nonzero = false;
        for (int i = 0; i < SHA256_HASH_LENGTH; ++i) {
            if (item->fingerprint[i] != 0) {
                found_nonzero = true;
                break;
            }
        }
        if (found_nonzero) {
            return item->fingerprint;
        }
    }

    return NULL;
}

// Calculate the "fingerprint" of a Decl
static void compute_decl_fingerprint(struct StackedHashTable *global_env,
                                     struct Decl *decl,
                                     uint8_t fingerprint[SHA256_HASH_LENGTH])
{
    struct SHA256_CTX ctx;
    sha256_init(&ctx);

    // Start with "DECL-CHKSUM\0" + the decl's checksum
    const char *decl_chksum = "DECL-CHKSUM";
    sha256_add_bytes(&ctx, (const uint8_t*) decl_chksum, strlen(decl_chksum)+1);
    sha256_add_bytes(&ctx, decl->checksum, SHA256_HASH_LENGTH);

    // Add "DECL-INT-FPR\0" + the corresponding interface decl's fingerprint,
    // if applicable.
    const uint8_t *interface_fingerprint = lookup_decl_fingerprint(global_env, decl->name);
    if (interface_fingerprint) {
        const char *decl_int_fpr = "DECL-INT-FPR";
        sha256_add_bytes(&ctx, (const uint8_t*) decl_int_fpr, strlen(decl_int_fpr)+1);
        sha256_add_bytes(&ctx, interface_fingerprint, SHA256_HASH_LENGTH);
    }

    // Add "DEP-FPR\0" + the fingerprint of any other decl that this one
    // (directly) depends on (in alphabetical order).
    for (struct NameList *node = decl->dependency_names; node; node = node->next) {
        const uint8_t* fingerprint_result = lookup_decl_fingerprint(global_env, node->name);
        if (!fingerprint_result) {
            fatal_error("could not find fingerprint for decl");
        }
        const char *dep_fpr = "DEP-FPR";
        sha256_add_bytes(&ctx, (const uint8_t*) dep_fpr, strlen(dep_fpr)+1);
        sha256_add_bytes(&ctx, fingerprint_result, SHA256_HASH_LENGTH);
    }

    sha256_final(&ctx, fingerprint);
}

static void verify_decl(struct VContext *context, struct Decl *decl)
{
    // Compute fingerprint.
    uint8_t fingerprint[SHA256_HASH_LENGTH];
    compute_decl_fingerprint(context->stack, decl, fingerprint);

    bool skipped = false;
    if (context->run_solver && sha256_exists_in_db(context->cache_db, DECL_HASH, fingerprint)) {
        skipped = true;
        context->run_solver = false;
    }

    if (context->show_progress) {
        // Add a "dummy" job to print the "Verifying:" message at the appropriate
        // point in the job queue.
        char *new_name = sanitise_name(decl->name);
        const char *msg_tail = skipped ? " (cached)\n" : "\n";
        char *msg = copy_string_3("Verifying: ", new_name, msg_tail);
        free(new_name);
        add_fol_message(msg, false, 0, NULL);
    }

    context->path_condition = make_string_sexpr("true");

    context->current_decl_name = decl->name;

    context->stack = push_verifier_stack(context->stack);  // make a new layer for local variables

    // verify the decl
    switch (decl->tag) {
    case DECL_CONST:
        verify_const_decl(context, decl->name, &decl->const_data, fingerprint);
        break;

    case DECL_FUNCTION:
        verify_function_decl(context, decl, fingerprint);
        break;

    case DECL_DATATYPE:
        verify_datatype_decl(context, decl, fingerprint);
        break;

    case DECL_TYPEDEF:
        verify_typedef_decl(context, decl, fingerprint);
        break;
    }

    // Clean up afterwards
    context->stack = pop_verifier_stack(context->stack);  // remove the local variables
    hash_table_clear(context->local_counter);
    hash_table_clear(context->local_to_version);
    clear_refs_hash_table(context->refs);

    free_sexpr(context->path_condition);
    context->path_condition = NULL;

    free_sexpr(context->facts);
    context->facts = NULL;
    context->num_facts = 0;

    hash_table_clear(context->local_hidden);

    clear_string_names_hash_table(context->string_names);
    context->current_decl_name = NULL;

    // On successful verification (in run_solver mode), add to DB
    if (context->run_solver) {
        add_fol_message(NULL, false, DECL_HASH, fingerprint);
    }

    // If skipped, restore run_solver to true for the next decl
    if (skipped) {
        context->run_solver = true;
    }
}

void verify_decl_group(struct VContext *context, struct Decl *decl_group)
{
    // for now no "per-group" setup required, just verify each decl separately
    struct Decl *decl = decl_group;

    while (decl && (!context->error_found || fol_continue_after_error())) {
        verify_decl(context, decl_group);
        decl = decl->next;
    }
}
