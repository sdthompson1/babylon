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

// 'context' is a (const struct Location **), pointing to the earliest
// origin location found so far (or NULL if none found yet).
static void * check_ty_univar(struct TypeTransform *tr, void *context, struct Type *type)
{
    const struct Location **found = context;
    struct UnivarNode *node = type->univar_data.node;

    if (node->type == NULL) {
        if (*found == NULL || location_before(&node->location, *found)) {
            *found = &node->location;
        }
    } else {
        // Check the resolved type itself (it might contain further univars).
        transform_type(tr, context, node->type);
    }

    return NULL;
}

static void check_type(const struct Location **found, struct Type *type)
{
    struct TypeTransform tr = {0};
    tr.nr_transform_univar = check_ty_univar;
    transform_type(&tr, found, type);
}

const struct Location * find_unresolved_univar_in_type(struct Type *type)
{
    const struct Location *found = NULL;
    check_type(&found, type);
    return found;
}

static void check_type_fn(void *context, struct Type **type)
{
    check_type(context, *type);
}

const struct Location * find_unresolved_univar_in_term(struct Term *term)
{
    const struct Location *found = NULL;
    forall_types_in_term(check_type_fn, &found, term);
    return found;
}

const struct Location * find_unresolved_univar_in_statement(struct Statement *stmt)
{
    const struct Location *found = NULL;
    forall_types_in_statement(check_type_fn, &found, stmt);
    return found;
}

const struct Location * find_unresolved_univar_in_decl(struct Decl *decl)
{
    const struct Location *found = NULL;
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
