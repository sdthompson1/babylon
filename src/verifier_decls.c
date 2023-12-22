/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "hash_table.h"
#include "sexpr.h"
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

static bool verify_const_decl(struct VContext *context,
                              const char *name,
                              struct DeclData_Const *data)
{
    bool ok = true;
    char *fol_name = copy_string_2("%", name);
    struct Sexpr *fol_type = verify_type(data->type);
    struct Sexpr *fol_term = NULL;

    if (data->rhs) {
        // Verify that the original rhs doesn't contain any errors
        // (e.g. division by zero)
        fol_term = verify_term(context, data->rhs);
        if (!fol_term) {
            ok = false;
        } else if (data->value) {
            // Now replace fol_term with data->value (original rhs reduced
            // to normal form).
            // This is done for two reasons:
            // (1) Optimisation: the normal form is usually shorter and
            //     easier for the solver to deal with.
            // (2) Correctness: some term types (record-updates in
            //     particular) rely on inserting special symbols (like
            //     "$RecordUpdate") into the local env. This wouldn't work
            //     for a global const decl. These terms do not occur in
            //     normal forms, so using the normal form will be safe.
            free_sexpr(fol_term);
            fol_term = verify_term(context, data->value);
            if (!fol_term) fatal_error("normal form failed to verify");
        }
    }

    add_const_item(context, fol_name, data->type, fol_type, fol_term, false);

    return ok;
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

static bool verify_function_attributes(struct VContext *context,
                                       struct Attribute *attr,
                                       struct Type *ret_type,
                                       struct Condition ***precond_tail,
                                       struct Condition ***postcond_tail)
{
    bool ok = true;
    int num_facts_after_requires = get_num_facts(context);

    while (attr) {
        switch (attr->tag) {
        case ATTR_REQUIRES:
        case ATTR_ENSURES:
            {
                struct Sexpr *cond = verify_term(context, attr->term);

                if (cond) {
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

                } else {
                    ok = false;
                }
            }
            break;

        case ATTR_INVARIANT:
        case ATTR_DECREASES:
            fatal_error("unexpected function attribute");
        }

        attr = attr->next;
    }

    // remove the postconditions afterwards (but not the preconditions)
    revert_facts(context, num_facts_after_requires);

    return ok;
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

static bool check_implies(struct VContext *context,
                          struct Location loc,
                          struct Sexpr *theta_premises_1,
                          struct Condition *premises_1,
                          struct Sexpr *theta_premises_2,
                          struct Condition *premises_2,
                          struct Sexpr *theta_conclusions,
                          struct Condition *conclusions)
{
    if (!conclusions) {
        // there is nothing to check
        return true;
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

    bool result = verify_condition(context, loc, sexpr, "interface consistency");
    free_sexpr(sexpr);
    return result;
}

static struct Sexpr * make_generic_fun_params(const struct TyVarList *tyvars)
{
    struct Sexpr *list = NULL;
    struct Sexpr **tail = &list;
    while (tyvars) {
        // Each type variable expands into three generic params:
        //  - the type itself
        //  - a default value of that type
        //  - a function telling whether a value of the type is "allocated" or not.
        *tail = make_list1_sexpr(make_string_sexpr_handover(copy_string_2("%", tyvars->name)));
        tail = &((*tail)->right);

        *tail = make_list1_sexpr(make_string_sexpr_handover(copy_string_2("$default-%", tyvars->name)));
        tail = &((*tail)->right);

        *tail = make_list1_sexpr(make_string_sexpr_handover(copy_string_2("$allocated-%", tyvars->name)));
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

static bool verify_function_decl(struct VContext *context,
                                 struct Decl *decl)
{
    // First let's see if there is an existing (interface) definition for this function
    char *fol_name = copy_string_2("%", decl->name);
    struct Item *interface_item = hash_table_lookup(context->global_env, fol_name);

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
    item->fol_decl = make_list4_sexpr(make_string_sexpr("declare-fun"),
                                      make_string_sexpr(fol_name),
                                      type_list,
                                      copy_sexpr(fol_fake_ret_type));
    type_list = NULL;

    item->fol_axioms = NULL;
    item->fol_name = copy_string(fol_name);
    item->fol_type = NULL;

    // Verify the preconds/postconds, and add the preconds to the list of known facts
    struct Condition *preconds = NULL;
    struct Condition **precond_tail = &preconds;
    struct Condition *postconds = NULL;
    struct Condition **postcond_tail = &postconds;
    bool ok = verify_function_attributes(context,
                                         decl->attributes,
                                         data->return_type,
                                         &precond_tail,
                                         &postcond_tail);

    // set funapp_sexpr to (%f %x %y)
    // (or just %f if no args)
    if (name_list == NULL) {
        context->funapp_sexpr = make_string_sexpr(fol_name);
    } else {
        context->funapp_sexpr =
            make_pair_sexpr(make_string_sexpr(fol_name), copy_sexpr(name_list));
    }


    if (data->body_specified) {
        context->postconds = postconds;

        struct Sexpr *fun_defn_expr = NULL;
        struct Sexpr **fun_defn_tail = &fun_defn_expr;
        ok = verify_statements(context, data->body, &fun_defn_tail) && ok;

        if (context->var_decl_stack != NULL) {
            fatal_error("var decl stack not empty");
        }

        if (decl->function_data.return_type) {
            // End of non-void function
            // Verify that this is unreachable code
            struct Sexpr *false_expr = make_string_sexpr("false");
            bool verify_result = verify_condition(context,
                                                  decl->function_data.end_loc,
                                                  false_expr,
                                                  "end of function unreachable");
            free_sexpr(false_expr);
            if (!verify_result) {
                report_end_of_function_reached(decl->function_data.end_loc);
                ok = false;
            }
        } else {
            // End of void function
            // Verify that the postconditions hold
            ok = verify_function_return(context, decl->function_data.end_loc,
                                        NULL, decl->ghost, &fun_defn_tail) && ok;
        }

        context->postconds = NULL;

        // If we got a fun_defn_expr then let's change our declare-fun into
        // a define-fun.
        if (fun_defn_expr != NULL) {
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
            }
        }
    }

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
    struct Sexpr *generic_vars = make_generic_fun_params(data->tyvars);
    make_generic(&item->fol_decl, item->fol_name, generic_vars);
    make_generic_list(item->fol_axioms, item->fol_name, generic_vars);

    // Save pre/post conditions to the Item
    item->fol_generic_vars = generic_vars;
    item->fol_dummies = name_list;
    name_list = NULL;

    item->preconds = preconds;
    preconds = NULL;

    item->postconds = postconds;
    postconds = NULL;

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
        if (!check_implies(context,
                           decl->location,
                           theta, interface_item->preconds,
                           NULL, NULL,
                           NULL, item->preconds)) {
            report_inconsistent_preconds(decl);
            ok = false;
        }
        if (!check_implies(context,
                           decl->location,
                           theta, interface_item->preconds,
                           NULL, item->postconds,
                           theta, interface_item->postconds)) {
            report_inconsistent_postconds(decl);
            ok = false;
        }
        free_sexpr(theta);
    }

    // Done, add Item to the env.
    remove_existing_item(context->global_env, fol_name);
    hash_table_insert(context->global_env, fol_name, item);

    return ok;
}

static bool verify_typedef_decl(struct VContext *context, struct Decl *decl)
{
    // If rhs != NULL we have a typedef (e.g. type Foo = Bar;). This
    // would already have been substituted away by the typechecker, so
    // we do not need to consider it here.

    // If rhs == NULL we are declaraing a new abstract type (e.g. type
    // Foo;). We need to do a "declare-sort" in this case.

    if (decl->typedef_data.rhs == NULL) {
        add_tyvar_to_env(context, decl->name, false,
                         decl->typedef_data.allocated ? ALLOC_ALWAYS : ALLOC_NEVER);
    }

    return true;
}

static bool verify_decl(struct VContext *context, struct Decl *decl)
{
    if (context->show_progress) {
        fprintf(stderr, "Verifying: ");
        for (const char *c = decl->name; *c; ++c) {
            if (*c != '^') {
                fputc(*c, stderr);
            }
        }
        fprintf(stderr, "\n");
    }

    bool result = false;

    context->path_condition = make_string_sexpr("true");

    // verify the decl
    switch (decl->tag) {
    case DECL_CONST:
        result = verify_const_decl(context, decl->name, &decl->const_data);
        break;

    case DECL_FUNCTION:
        result = verify_function_decl(context, decl);
        break;

    case DECL_DATATYPE:
        // Nothing needed
        result = true;
        break;

    case DECL_TYPEDEF:
        result = verify_typedef_decl(context, decl);
        break;
    }

    // clean up afterwards
    clear_verifier_env_hash_table(context->local_env);
    hash_table_clear(context->local_counter);
    clear_refs_hash_table(context->refs);

    free_sexpr(context->path_condition);
    context->path_condition = NULL;

    free_sexpr(context->facts);
    context->facts = NULL;
    context->num_facts = 0;

    hash_table_clear(context->local_hidden);

    return result;
}

bool verify_decl_group(struct VContext *context, struct Decl *decl_group)
{
    // for now no "per-group" setup required, just verify each decl separately
    bool ok = true;
    struct Decl *decl = decl_group;

    while (decl && (!context->error_found || context->continue_after_error)) {
        ok = verify_decl(context, decl_group) && ok;
        decl = decl->next;
    }

    return ok;
}
