/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "ast.h"
#include "error.h"
#include "remove_univars.h"

#include <stdlib.h>

static void * remove_ty_univar(struct TypeTransform *tr, void *context, struct Type *type)
{
    struct Type *base_type = NULL;

    if (--(type->univar_data.node->ref_count) > 0) {
        // The node is still active elsewhere, so copy the base type.
        base_type = copy_type(type->univar_data.node->type);
    } else {
        // This is the last usage of this node, so just "take out" the base type,
        // then free the node.
        base_type = type->univar_data.node->type;
        free(type->univar_data.node);
    }

    // "Shallow copy" the base_type into *type, then free base_type.
    if (base_type) {
        *type = *base_type;
        free(base_type);

        // Ensure that the copied type does not itself include any TY_UNIVARs...
        transform_type(tr, context, type);

    } else {
        // No type could be inferred, so we (arbitrarily) set it to TY_BOOL.
        type->tag = TY_BOOL;
    }

    return NULL;
}

void remove_univars_from_type(struct Type *type)
{
    struct TypeTransform tr = {0};
    tr.nr_transform_univar = remove_ty_univar;
    transform_type(&tr, NULL, type);
}

void remove_univars_from_term(struct Term *term)
{
    struct TermTransform tr = {0};
    tr.type_transform.nr_transform_univar = remove_ty_univar;
    transform_term(&tr, NULL, term);
}

void remove_univars_from_attribute(struct Attribute *attr)
{
    while (attr) {
        switch (attr->tag) {
        case ATTR_REQUIRES:
        case ATTR_ENSURES:
        case ATTR_INVARIANT:
        case ATTR_DECREASES:
            remove_univars_from_term(attr->term);
            break;
        }

        attr = attr->next;
    }
}

void remove_univars_from_statement(struct Statement *stmt)
{
    while (stmt) {
        switch (stmt->tag) {
        case ST_VAR_DECL:
            remove_univars_from_type(stmt->var_decl.type);
            remove_univars_from_term(stmt->var_decl.rhs);
            break;

        case ST_FIX:
            remove_univars_from_type(stmt->fix.type);
            break;

        case ST_OBTAIN:
            remove_univars_from_type(stmt->obtain.type);
            remove_univars_from_term(stmt->obtain.condition);
            break;

        case ST_USE:
            remove_univars_from_term(stmt->use.term);
            break;

        case ST_ASSIGN:
            remove_univars_from_term(stmt->assign.lhs);
            remove_univars_from_term(stmt->assign.rhs);
            break;

        case ST_SWAP:
            remove_univars_from_term(stmt->swap.lhs);
            remove_univars_from_term(stmt->swap.rhs);
            break;

        case ST_RETURN:
            remove_univars_from_term(stmt->ret.value);
            break;

        case ST_ASSERT:
            remove_univars_from_term(stmt->assert_data.condition);
            remove_univars_from_statement(stmt->assert_data.proof);
            break;

        case ST_ASSUME:
            remove_univars_from_term(stmt->assume.condition);
            break;

        case ST_IF:
            remove_univars_from_term(stmt->if_data.condition);
            remove_univars_from_statement(stmt->if_data.then_block);
            remove_univars_from_statement(stmt->if_data.else_block);
            break;

        case ST_WHILE:
            remove_univars_from_term(stmt->while_data.condition);
            remove_univars_from_attribute(stmt->while_data.attributes);
            remove_univars_from_statement(stmt->while_data.body);
            break;

        case ST_CALL:
            remove_univars_from_term(stmt->call.term);
            break;

        case ST_MATCH:
            remove_univars_from_term(stmt->match.scrutinee);
            for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {
                remove_univars_from_statement(arm->rhs);
            }
            break;

        case ST_MATCH_FAILURE:
            break;

        case ST_SHOW_HIDE:
            break;
        }

        stmt = stmt->next;
    }
}

void remove_univars_from_decl(struct Decl *decl)
{
    while (decl) {

        switch (decl->tag) {
        case DECL_CONST:
            remove_univars_from_type(decl->const_data.type);
            remove_univars_from_term(decl->const_data.rhs);
            remove_univars_from_term(decl->const_data.value);
            break;

        case DECL_FUNCTION:
            for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
                remove_univars_from_type(arg->type);
            }
            remove_univars_from_type(decl->function_data.return_type);
            remove_univars_from_statement(decl->function_data.body);
            break;

        case DECL_DATATYPE:
        case DECL_TYPEDEF:
            // These cases shouldn't be required, because TY_UNIVAR nodes are never
            // created in datatypes or typedefs.
            fatal_error("not implemented");
        }

        remove_univars_from_attribute(decl->attributes);

        decl = decl->next;
    }
}
