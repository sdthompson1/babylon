/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2026.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "ast.h"
#include "error.h"
#include "hash_table.h"
#include "subst_type.h"
#include "util.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void * subst_ty_var(void *context, struct Type *type)
{
    struct Type *target = hash_table_lookup(context, type->var_data.name);
    if (target) {
        return copy_type(target);
    } else {
        return copy_type(type);
    }
}

static void * subst_ty_forall_or_lambda(void *context, struct Type *type, void *tyvars_result, void *child_type_result)
{
    // to do this properly would require careful treatment of variable capture
    // luckily we do not need this for now
    fatal_error("substitute_in_type: unimplemented case");
}

struct Type * substitute_in_type_from_hashtable(struct HashTable *theta,
                                                const struct Type *type)
{
    struct TypeTransform tr = {0};
    copying_type_transform(&tr);
    tr.transform_var = subst_ty_var;
    tr.transform_forall = subst_ty_forall_or_lambda;
    tr.transform_lambda = subst_ty_forall_or_lambda;
    return transform_type(&tr, theta, (struct Type*)type);
}

struct Type * substitute_in_type_from_list(struct TyVarList *tyvars,
                                           struct TypeList *tyargs,
                                           const struct Type *type)
{
    struct HashTable *theta = new_hash_table();

    while (tyvars && tyargs) {
        hash_table_insert(theta, tyvars->name, tyargs->type);
        tyvars = tyvars->next;
        tyargs = tyargs->next;
    }

    struct Type *result = substitute_in_type_from_hashtable(theta, type);

    free_hash_table(theta);
    return result;
}


// ------------------------------------------------------------------

// Capture-avoiding substitution of types in decls

// First, algorithm to check if a certain name appears free in a type.
// The name is the 'context' variable.

// These helper functions return context to mean 'true' or NULL for 'false'.

static void * check_var(void *context, struct Type *type_var)
{
    if (strcmp(type_var->var_data.name, context) == 0) {
        return context;
    } else {
        return NULL;
    }
}

static void * passthrough_1(void *context, struct Type *type, void *child_result)
{
    return child_result;
}

static void * passthrough_2(void *context, struct Type *type, void *child_1, void *child_2)
{
    if (child_1 != NULL || child_2 != NULL) {
        return context;
    } else {
        return NULL;
    }
}

static void * check_lambda_or_forall(void *context, struct Type *type_forall, void *tyvars_result, void *child_type_result)
{
    if (tyvars_result) {
        // The variable appeared as a dummy of this lambda/forall, so it is not free
        return NULL;
    }
    // Otherwise, var is free iff it is free in the body.
    return child_type_result;
}

static void * check_univar(struct TypeTransform *tr, void *context, struct Type *type)
{
    // There shouldn't be any univars at the point when this function is called.
    fatal_error("is_var_free_in_type: unexpected TY_UNIVAR found");
}

static void * check_tyvar_list(void *context, struct TyVarList *node, void *next_result)
{
    // This function just detects whether context (a string) appears anywhere in the TyVarList.
    if (next_result) {
        return next_result;
    }
    if (strcmp(node->name, context) == 0) {
        return context;
    }
    return NULL;
}

static void * check_type_list(void *context, struct TypeList *node, void *type_result, void *next_result)
{
    // This is for things like TYAPP nodes
    if (type_result != NULL || next_result != NULL) {
        return context;
    } else {
        return NULL;
    }
}

static void * check_name_type_list(void *context, struct NameTypeList *node, void *type_result, void *next_result)
{
    // This is for things like records or variants
    if (type_result != NULL || next_result != NULL) {
        return context;
    } else {
        return NULL;
    }
}

static void * check_fun_arg(void *context, struct FunArg *node, void *type_result, void *next_result)
{
    // This is for function arguments
    if (type_result != NULL || next_result != NULL) {
        return context;
    } else {
        return NULL;
    }
}

static struct TypeTransform IS_VAR_FREE_TRANSFORM = {
    .transform_var = check_var,
    // transform_bool, finite_int, math_int, math_real deliberately left as NULL
    .transform_record = passthrough_1,
    .transform_variant = passthrough_1,
    .transform_array = passthrough_1,
    .transform_function = passthrough_2,
    .transform_forall = check_lambda_or_forall,
    .transform_lambda = check_lambda_or_forall,
    .transform_app = passthrough_2,
    .nr_transform_univar = check_univar,
    .transform_tyvar_list = check_tyvar_list,
    .transform_type_list = check_type_list,
    .transform_name_type_list = check_name_type_list,
    .transform_fun_arg = check_fun_arg
};

static bool is_var_free_in_type(const char *name, struct Type *type)
{
    return transform_type(&IS_VAR_FREE_TRANSFORM, (void*)name, type) != NULL;
}


static bool tyvar_list_contains_name(struct TyVarList *list, const char *name)
{
    while (list) {
        if (strcmp(list->name, name) == 0) {
            return true;
        }
        list = list->next;
    }
    return false;
}

static char* make_fresh_name(const char *base_name, struct Type *must_not_be_free_in)
{
    uint64_t number = 0;
    char buf[50];
    while (true) {
        sprintf(buf, "%" PRIu64, number);
        char *new_name = copy_string_2(base_name, buf);
        if (!is_var_free_in_type(new_name, must_not_be_free_in)) {
            return new_name;
        }
        free(new_name);
        ++number;
    }
}


static void substitute_type_in_place(const char *name, struct Type *replacement, struct Type **type)
{
    if (*type == NULL) {
        return;
    }

    switch ((*type)->tag) {
    case TY_UNIVAR:
        fatal_error("substitute_type_in_place: unimplemented case");

    case TY_VAR:
        if (strcmp((*type)->var_data.name, name) == 0) {
            free_type(*type);
            *type = copy_type(replacement);
        }
        break;

    case TY_BOOL:
    case TY_FINITE_INT:
    case TY_MATH_INT:
    case TY_MATH_REAL:
        break;

    case TY_RECORD:
        {
            for (struct NameTypeList *node = (*type)->record_data.fields; node; node = node->next) {
                substitute_type_in_place(name, replacement, &node->type);
            }
        }
        break;

    case TY_VARIANT:
        {
            for (struct NameTypeList *node = (*type)->variant_data.variants; node; node = node->next) {
                substitute_type_in_place(name, replacement, &node->type);
            }
        }
        break;

    case TY_ARRAY:
        substitute_type_in_place(name, replacement, &(*type)->array_data.element_type);
        break;

    case TY_FUNCTION:
        {
            for (struct FunArg *arg = (*type)->function_data.args; arg; arg = arg->next) {
                substitute_type_in_place(name, replacement, &arg->type);
            }
            substitute_type_in_place(name, replacement, &(*type)->function_data.return_type);
        }
        break;

    case TY_FORALL:
    case TY_LAMBDA:
        {
            struct TyVarList *dummies = (*type)->tag == TY_FORALL ? (*type)->forall_data.tyvars : (*type)->lambda_data.tyvars;
            struct Type **body = (*type)->tag == TY_FORALL ? &(*type)->forall_data.type : &(*type)->lambda_data.type;

            // If 'name' is one of the dummy vars, then don't substitute inside the body.
            if (tyvar_list_contains_name(dummies, name)) {
                break;
            }

            // If any of the dummy vars are free in 'replacement',
            // then we need to rename that dummy var.
            for (struct TyVarList *node = dummies; node; node = node->next) {
                if (is_var_free_in_type(node->name, replacement)) {
                    char *new_name = make_fresh_name(node->name, replacement);

                    struct Type ty;
                    ty.location = g_no_location;
                    ty.tag = TY_VAR;
                    ty.var_data.name = new_name;
                    substitute_type_in_place(node->name, &ty, body);

                    free((void*)node->name);
                    node->name = new_name;
                }
            }

            // Now we are free to do the substitution in the body.
            substitute_type_in_place(name, replacement, body);
        }
        break;

    case TY_APP:
        {
            substitute_type_in_place(name, replacement, &(*type)->app_data.lhs);
            for (struct TypeList *node = (*type)->app_data.tyargs; node; node = node->next) {
                substitute_type_in_place(name, replacement, &node->type);
            }
        }
        break;
    }
}

struct NameReplacement {
    const char *name;
    struct Type *replacement;
};

static void subst_type_fn(void *context, struct Type **type)
{
    struct NameReplacement *nr = context;
    substitute_type_in_place(nr->name, nr->replacement, type);
}

// Substitute 'name' to 'replacement' in every Type within the
// "DeclData" part of this decl (i.e. the const, function, etc.,
// specific part) and also the Attributes. Ignores the "tyvars" list
// if any, and does not look at 'next' decls.
static void do_substitute_type_in_decl(const char *name,
                                       struct Type *replacement,
                                       struct Decl *decl)
{
    struct NameReplacement context = {name, replacement};
    forall_types_in_decl(subst_type_fn, &context, decl);
}

static struct TyVarList *get_tyvars(struct Decl *decl)
{
    switch (decl->tag) {
    case DECL_CONST:
        return NULL;

    case DECL_FUNCTION:
        return decl->function_data.tyvars;

    case DECL_DATATYPE:
        return decl->datatype_data.tyvars;

    case DECL_TYPEDEF:
        return decl->typedef_data.tyvars;
    }

    fatal_error("wrong decl tag");
}


static void substitute_type_in_decls(const char *name,
                                     struct Type *replacement,
                                     struct Decl *decl,
                                     TypeEnv *type_env)
{
    for (; decl; decl = decl->next) {

        // Get tyvar list for this decl
        struct TyVarList *tyvars = get_tyvars(decl);

        // If 'name' is one of the tyvars, then no substitution is required in this decl.
        if (tyvar_list_contains_name(tyvars, name)) {
            continue;
        }

        // If any of the tyvars are free in 'replacement', then rename it
        for (struct TyVarList *node = tyvars; node; node = node->next) {
            if (is_var_free_in_type(node->name, replacement)) {
                char *new_name = make_fresh_name(node->name, replacement);

                struct Type ty;
                ty.location = g_no_location;
                ty.tag = TY_VAR;
                ty.var_data.name = new_name;
                do_substitute_type_in_decl(node->name, &ty, decl);

                free((void*)node->name);
                node->name = new_name;
            }
        }

        // Now we are free to do the substitution in the decl
        do_substitute_type_in_decl(name, replacement, decl);

        // Also substitute the type env entry, if any
        struct TypeEnvEntry *entry = type_env_lookup(type_env, decl->name);
        if (entry && entry->type) {
            substitute_type_in_place(name, replacement, &entry->type);
        }

        // Data constructors (for datatypes) have their own, separate
        // type env entries.
        if (decl->tag == DECL_DATATYPE) {
            for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
                struct TypeEnvEntry *ctor_entry = type_env_lookup(type_env, ctor->name);
                if (ctor_entry && ctor_entry->type) {
                    substitute_type_in_place(name, replacement, &ctor_entry->type);
                }
            }
        }
    }
}

void substitute_type_in_decl_group(const char *name,
                                   struct Type *replacement,
                                   struct DeclGroup *group,
                                   TypeEnv *type_env)
{
    while (group) {
        substitute_type_in_decls(name, replacement, group->decl, type_env);
        group = group->next;
    }
}
