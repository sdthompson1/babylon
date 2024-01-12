/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "hash_table.h"
#include "scc.h"
#include "sexpr.h"
#include "verifier_context.h"
#include "verifier_dependency.h"
#include "verifier_func.h"
#include "verifier_run.h"
#include "verifier_terms.h"
#include "verifier_types.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct Type *get_expanded_ret_type(struct FunArg *args, struct Type *ret_ty)
{
    struct Type *ret;
    if (ret_ty == NULL) {
        ret = make_type(g_no_location, TY_RECORD);
        ret->record_data.fields = NULL;
    } else {
        ret = copy_type(ret_ty);
    }

    struct NameTypeList *list = NULL;
    struct NameTypeList **tail = &list;

    for (; args; args = args->next) {
        if (args->ref) {
            *tail = alloc(sizeof(struct NameTypeList));
            (*tail)->name = NULL; // Since this is a fake type, we won't need field names.
            (*tail)->type = copy_type(args->type);
            (*tail)->next = NULL;
            tail = &(*tail)->next;
        }
    }

    if (list) {
        // make a TY_RECORD of ret + list
        struct NameTypeList *node = alloc(sizeof(struct NameTypeList));
        node->name = NULL;
        node->type = ret;
        node->next = list;

        struct Type *type = make_type(g_no_location, TY_RECORD);
        type->record_data.fields = node;

        return type;

    } else {
        // the return type is just ret
        return ret;
    }
}

struct Sexpr *ret_fldn(int n, struct Sexpr *fol_ret_ty)
{
    char buf[30];
    sprintf(buf, "$FLD%d", n);

    // fol_ret_ty is of the form (instance $PROD (things))
    if (!sexpr_equal_string(fol_ret_ty->left, "instance")) {
        fatal_error("ret_fldn sanity check failed");
    }

    // change it to (instance $FLDn (things))
    struct Sexpr *result = copy_sexpr(fol_ret_ty);
    free_sexpr(result->right->left);
    result->right->left = make_string_sexpr(buf);

    return result;
}

// validity handed over; fol_ret_ty copied
static struct Sexpr * ret_val_valid_expr(int n, struct Sexpr *fol_ret_ty, struct Sexpr *validity)
{
    return make_list3_sexpr(
        make_string_sexpr("let"),
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr("$ret_val"),
                make_list2_sexpr(
                    ret_fldn(n, fol_ret_ty),
                    make_string_sexpr("%return")))),
        validity);
}

struct Sexpr *ret_validity_test(struct FunArg *args, struct Type *ret_ty, struct Sexpr *fol_ret_ty)
{
    struct Sexpr *checks = NULL;
    struct Sexpr **tail = &checks;

    // field 0 of %return is the return value, and later fields are
    // the updated ref args.
    int n = 1;
    bool ref_found = false;

    for (struct FunArg *arg = args; arg; arg = arg->next) {
        if (arg->ref) {
            struct Sexpr *validity = validity_test_expr(arg->type, "$ret_val");
            if (validity) {
                *tail = make_list1_sexpr(ret_val_valid_expr(n, fol_ret_ty, validity));
                tail = &(*tail)->right;
            }
            ++n;
            ref_found = true;
        }
    }

    if (ref_found) {
        if (ret_ty) {
            struct Sexpr *validity = validity_test_expr(ret_ty, "$ret_val");
            if (validity) {
                *tail = make_list1_sexpr(ret_val_valid_expr(0, fol_ret_ty, validity));
                tail = &(*tail)->right;
            }
        }
        if (checks != NULL) {
            return conjunction(checks);
        } else {
            return NULL;
        }

    } else if (ret_ty) {
        // There are no ref-args, we just have to check %return itself is valid.
        return validity_test_expr(ret_ty, "%return");

    } else {
        // There are neither ref-args nor a return value
        return NULL;
    }
}

struct Sexpr * add_return_if_required(struct Sexpr *ret_defn, struct Sexpr *expr)
{
    if (sexpr_contains_string(expr, "%return")) {
        // (let ((%return RETVAL)) EXPR)
        return make_list3_sexpr(
            make_string_sexpr("let"),
            make_list1_sexpr(
                make_list2_sexpr(
                    make_string_sexpr("%return"),
                    ret_defn)),
            expr);
    } else {
        free_sexpr(ret_defn);
        return expr;
    }
}

// Creates a tuple of ret_val and updated ref args (of the current function).
// If there are no ref args, just returns a copy of ret_val.
// Returns false if errors were found (e.g. poisoned ref arguments).
static bool get_expanded_ret_val(struct VContext *context,
                                 struct Sexpr *ret_val,
                                 struct Sexpr **output)
{
    struct Sexpr *refs = NULL;
    struct Sexpr **tail = &refs;
    for (struct FunArg *arg = context->function_args; arg; arg = arg->next) {
        if (arg->ref) {
            const char *fol_name = lookup_local(context, arg->name);
            if (fol_name == NULL) {
                fatal_error("arg var not found in context");
            }
            if (hash_table_lookup(context->local_env, fol_name) == NULL) {
                // Ref arg is poisoned, give up
                free((char*)fol_name);
                free_sexpr(refs);
                *output = NULL;
                return false;
            }
            *tail = make_list1_sexpr(make_string_sexpr_handover(fol_name));
            tail = &(*tail)->right;
        }
    }

    if (refs) {
        // As it happens, the type of %return in the env, is also the
        // constructor we need for the result-tuple (an instance of
        // $PROD).
        struct Item *ret_item = hash_table_lookup(context->local_env, "%return");
        if (ret_item == NULL) {
            fatal_error("could not find %return in env");
        }
        struct Sexpr *ctor = copy_sexpr(ret_item->fol_type);

        struct Sexpr *head;
        if (ret_val) {
            head = copy_sexpr(ret_val);
        } else {
            head = make_string_sexpr("$PROD");
        }

        *output = make_pair_sexpr(ctor, make_pair_sexpr(head, refs));

    } else if (ret_val) {
        *output = copy_sexpr(ret_val);

    } else {
        *output = NULL;
    }

    return true;
}

static bool verify_postconditions(struct VContext *context,
                                  struct Location loc,
                                  struct Sexpr *expanded_ret_val)
{
    struct Condition *postconds = context->postconds;
    bool ok = true;

    while (postconds) {

        struct Sexpr *postcond_expr = copy_sexpr(postconds->expr);
        if (expanded_ret_val) {
            postcond_expr = add_return_if_required(copy_sexpr(expanded_ret_val), postcond_expr);
        }

        char buf1[500], buf2[520];
        format_location(&postconds->location, true, false, buf1, sizeof(buf1));
        snprintf(buf2, sizeof(buf2), "postcondition at %s", buf1);

        bool verify_result = verify_condition(context, loc, postcond_expr, buf2);
        if (!verify_result) {
            report_function_postcondition_fail(loc, postconds->location);
            ok = false;
        }

        free_sexpr(postcond_expr);

        postconds = postconds->next;
    }

    return ok;
}

static bool require_let_for(struct VContext *context, const char *name)
{
    if (strcmp(name, "%return") == 0) {
        // Lets not required for "%return"
        return false;
    }

    const char *prefix1 = "$allocated-";
    const char *prefix2 = "$default-";
    if (strncmp(prefix1, name, strlen(prefix1)) == 0
    || strncmp(prefix2, name, strlen(prefix2)) == 0) {
        // Lets not required for "$default" or "$allocated" variables because
        // these will become part of the generic args for this function.
        return false;
    }

    struct Sexpr *arg_list = context->arglist_sexpr;
    while (arg_list) {
        if (strcmp(name, arg_list->left->left->string) == 0) {
            // Lets not required for formal arguments of the function.
            return false;
        }
        arg_list = arg_list->right;
    }

    return true;
}

struct Sexpr * insert_lets(struct VContext *context,
                           struct Sexpr *expr)
{
    struct Sexpr *deps = get_sexpr_dependencies(context->local_env, NULL, NULL, expr, NULL);

    // First of all, figure out which deps we want to keep.
    struct Sexpr *new_deps = NULL;
    struct Sexpr **tail_ptr = &new_deps;

    while (deps) {
        struct Sexpr *defn = deps->left;
        struct Sexpr *next = deps->right;
        free(deps);

        // Figure out the name.
        // The only things in the local_env should be
        // define-fun, declare-fun, declare-const,
        // declare-sort, assert.
        // (The latter two can be ignored.)
        const char *name = NULL;
        if (sexpr_equal_string(defn->left, "define-fun")
        || sexpr_equal_string(defn->left, "declare-fun")
        || sexpr_equal_string(defn->left, "declare-const")) {
            name = defn->right->left->string;
        } else if (sexpr_equal_string(defn->left, "declare-sort")
        || sexpr_equal_string(defn->left, "assert")) {
            // Ignore
        } else {
            fatal_error("insert_lets: unrecognised local_env dependency");
        }

        // We don't need to insert lets for certain variable names.
        if (name && require_let_for(context, name)) {

            // Keep this dependency.
            *tail_ptr = make_list1_sexpr(defn);
            tail_ptr = &(*tail_ptr)->right;

            defn = NULL;
        }

        free_sexpr(defn);
        deps = next;
    }

    // Now sort the deps into the proper order (we want "reverse" order
    // because we will be creating lets "inside out").
    new_deps = reorder_sexpr_defns(new_deps, true);

    // Now create the lets.
    while (new_deps) {
        struct Sexpr *defn = new_deps->left;
        struct Sexpr *next = new_deps->right;
        free(new_deps);

        if (expr != NULL) {

            // Only defns of the form
            // (define-fun name () type value)
            // can be used.

            if (!sexpr_equal_string(defn->left, "define-fun")
            || defn->right->right->left != NULL) {
                free_sexpr(expr);
                expr = NULL;

            } else {
                struct Sexpr **name = &defn->right->left;
                struct Sexpr **value = &defn->right->right->right->right->left;

                // Add a let for this variable
                // (let ((var value)) expr)
                expr = make_list3_sexpr(
                    make_string_sexpr("let"),
                    make_list1_sexpr(
                        make_list2_sexpr(
                            *name,
                            *value)),
                    expr);
                *name = NULL;
                *value = NULL;
            }
        }

        free_sexpr(defn);
        new_deps = next;
    }

    return expr;
}

bool verify_function_return(struct VContext *context,
                            struct Location location,
                            struct Term *return_term,
                            bool ghost,
                            struct Sexpr *** ret_val_ptr)
{
    // If this point in the code is unreachable we shouldn't try to continue
    if (sexpr_equal_string(context->path_condition, "false")) {
        return true;
    }

    bool ok = true;
    struct Sexpr *ret_val = NULL;

    if (return_term) {
        ret_val = verify_term(context, return_term);
        if (!ret_val) {
            // Verification of return-value failed, no point continuing
            free_sexpr(context->path_condition);
            context->path_condition = make_string_sexpr("false");
            return false;
        }

        // Verify the value being returned is not allocated (except in ghost code)
        if (!ghost) {
            struct Sexpr *cond = non_allocated_condition(context, return_term->type, ret_val);
            if (cond) {
                bool verify_result = verify_condition(context, location, cond, "return value not allocated");
                if (!verify_result) {
                    report_return_allocated(location);
                    ok = false;
                }

                free_sexpr(cond);
            }
        }
    }

    // Expand the ret val to include "new" values of ref vars
    struct Sexpr *expanded_ret_val;
    bool ret_val_valid = get_expanded_ret_val(context, ret_val, &expanded_ret_val);
    free_sexpr(ret_val);

    if (ret_val_valid) {
        // Verify that under the current path condition, each
        // postcondition is true at this point
        ok = verify_postconditions(context, location, expanded_ret_val) && ok;

        if (expanded_ret_val != NULL) {
            // Add (ite current-path-condition expr NULL) onto the definition
            // of this function.
            // ("ret_val_ptr" always points to the NULL at the tail of this chain.)
            make_ite_pc_expr(ret_val_ptr, context, expanded_ret_val);
            expanded_ret_val = NULL;
        }
    }

    free_sexpr(expanded_ret_val);

    free_sexpr(context->path_condition);
    context->path_condition = make_string_sexpr("false");

    return ok;
}
