/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "ast.h"
#include "error.h"
#include "hash_table.h"

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
