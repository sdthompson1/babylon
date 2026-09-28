/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2026.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "ast.h"
#include "remove_univars.h"

#include <stdlib.h>


// ----------------------------------------------------------------------------------------------------
// Checking for unresolved univars

static void * check_ty_univar(struct TypeTransform *tr, void *context, struct Type *type)
{
    bool *found_unresolved = context;
    struct UnivarNode *node = type->univar_data.node;

    if (node->type == NULL) {
        *found_unresolved = true;
    } else {
        // Check the resolved type itself (it might contain further univars).
        transform_type(tr, context, node->type);
    }

    return NULL;
}

bool type_contains_unresolved_univars(struct Type *type)
{
    bool found_unresolved = false;
    struct TypeTransform tr = {0};
    tr.nr_transform_univar = check_ty_univar;
    transform_type(&tr, &found_unresolved, type);
    return found_unresolved;
}

static void check_type_fn(void *context, struct Type **type)
{
    bool *found = context;
    if (type_contains_unresolved_univars(*type)) {
        *found = true;
    }
}

bool term_contains_unresolved_univars(struct Term *term)
{
    bool found = false;
    forall_types_in_term(check_type_fn, &found, term);
    return found;
}

bool statement_contains_unresolved_univars(struct Statement *stmt)
{
    bool found = false;
    forall_types_in_statement(check_type_fn, &found, stmt);
    return found;
}

bool decl_contains_unresolved_univars(struct Decl *decl)
{
    bool found = false;
    forall_types_in_decl(check_type_fn, &found, decl);
    return found;
}


// ----------------------------------------------------------------------------------------------------
// Removing univars

static void * remove_ty_univar(struct TypeTransform *tr, void *context, struct Type *type)
{
    struct UnivarNode *node = type->univar_data.node;

    if (node->type == NULL) {
        // Unresolved univar - do nothing
        return NULL;
    }

    struct Type *base_type = NULL;

    if (--(node->ref_count) > 0) {
        // The node is still active elsewhere, so copy the base type.
        base_type = copy_type(node->type);
    } else {
        // This is the last usage of this node, so just "take out" the base type,
        // then free the node.
        base_type = node->type;
        free(node);
    }

    // Shallow-copy the base_type into *type, then free base_type.
    *type = *base_type;
    free(base_type);

    // Ensure that the copied type does not itself include any TY_UNIVARs.
    transform_type(tr, context, type);

    return NULL;
}

void remove_univars_from_type(struct Type *type)
{
    struct TypeTransform tr = {0};
    tr.nr_transform_univar = remove_ty_univar;
    transform_type(&tr, NULL, type);
}

static void remove_type_fn(void *context, struct Type **type)
{
    remove_univars_from_type(*type);
}

void remove_univars_from_term(struct Term *term)
{
    forall_types_in_term(remove_type_fn, NULL, term);
}

void remove_univars_from_statement(struct Statement *stmt)
{
    forall_types_in_statement(remove_type_fn, NULL, stmt);
}

void remove_univars_from_decl(struct Decl *decl)
{
    forall_types_in_decl(remove_type_fn, NULL, decl);
}
