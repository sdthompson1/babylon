/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#include "ast.h"
#include "error.h"
#include "names.h"
#include "hash_table.h"

#include <stddef.h>

void names_used_in_term(struct HashTable *names, struct Term *term);


//
// Types
//

static void * names_tyvar(void *context, struct Type *type)
{
    hash_table_insert(context, type->var_data.name, NULL);
    return NULL;
}

static void * names_tyvar_list(void *context, struct TyVarList *node, void *next_result)
{
    hash_table_insert(context, node->name, NULL);
    return NULL;
}

static void * names_fixed_array(void *context, struct Type *type, void *elt_type_result)
{
    // A quirk of TypeTransform is that it does not descend into
    // the terms found in TY_FIXED_ARRAY, therefore we have to do that
    // ourselves here.
    for (int i = 0; i < type->fixed_array_data.ndim; ++i) {
        names_used_in_term(context, type->fixed_array_data.sizes[i]);
    }
    return NULL;
}

static void names_type_transform(struct TypeTransform *transform)
{
    transform->transform_var = names_tyvar;
    transform->transform_tyvar_list = names_tyvar_list;
    transform->transform_fixed_array = names_fixed_array;
}

void names_used_in_type(struct HashTable *names, struct Type *type)
{
    struct TypeTransform transform = {0};
    names_type_transform(&transform);
    transform_type(&transform, names, type);
}


//
// Terms
//

static void * names_var_term(void *context, struct Term *term, void *type_result)
{
    hash_table_insert(context, term->var.name, NULL);
    return NULL;
}

static void * names_let_term(void *context, struct Term *term, void *type_result, void *rhs_result, void *body_result)
{
    hash_table_insert(context, term->let.name, NULL);
    return NULL;
}

static void * names_quantifier_term(void *context, struct Term *term, void *type_result, void *var_type_result, void *rhs_result)
{
    hash_table_insert(context, term->quant.name, NULL);
    return NULL;
}

static void names_used_in_pattern(struct HashTable *names, struct Pattern *pattern)
{
    if (pattern == NULL) return;

    switch (pattern->tag) {
    case PAT_VAR:
        hash_table_insert(names, pattern->var.name, NULL);
        break;

    case PAT_BOOL:
    case PAT_INT:
        break;

    case PAT_RECORD:
        for (struct NamePatternList *node = pattern->record.fields; node; node = node->next) {
            names_used_in_pattern(names, node->pattern);
        }
        break;

    case PAT_VARIANT:
        names_used_in_pattern(names, pattern->variant.payload);
        break;

    case PAT_WILDCARD:
        break;
    }
}

static void * names_arm(void *context, struct Arm *arm, void *rhs_result, void *next_result)
{
    // patterns aren't covered by the transform framework so we have
    // to call names_used_in_pattern explicitly
    names_used_in_pattern(context, arm->pattern);
    return NULL;
}

void names_used_in_term(struct HashTable *names, struct Term *term)
{
    // We only need to care about TM_VAR, TM_LET and TM_QUANTIFIER (and any types)
    // and also patterns (transform_arm)
    // Note: record field names and variant names are not considered
    // "names" for our purposes
    struct TermTransform transform = {0};
    transform.transform_var = names_var_term;
    transform.transform_let = names_let_term;
    transform.transform_quantifier = names_quantifier_term;
    transform.transform_arm = names_arm;
    names_type_transform(&transform.type_transform);
    transform_term(&transform, names, term);
}


//
// Statements
//

static void names_used_in_attributes(struct HashTable *names, struct Attribute *attr)
{
    while (attr) {
        switch (attr->tag) {
        case ATTR_REQUIRES:
        case ATTR_ENSURES:
        case ATTR_INVARIANT:
        case ATTR_DECREASES:
            names_used_in_term(names, attr->term);
            break;
        }

        attr = attr->next;
    }
}

void names_used_in_statements(struct HashTable *names, struct Statement *stmt)
{
    while (stmt) {
        switch (stmt->tag) {
        case ST_VAR_DECL:
            hash_table_insert(names, stmt->var_decl.name, NULL);
            names_used_in_type(names, stmt->var_decl.type);
            names_used_in_term(names, stmt->var_decl.rhs);
            break;

        case ST_FIX:
            hash_table_insert(names, stmt->fix.name, NULL);
            names_used_in_type(names, stmt->fix.type);
            break;

        case ST_OBTAIN:
            hash_table_insert(names, stmt->obtain.name, NULL);
            names_used_in_type(names, stmt->obtain.type);
            names_used_in_term(names, stmt->obtain.condition);
            break;

        case ST_USE:
            names_used_in_term(names, stmt->use.term);
            break;

        case ST_ASSIGN:
            names_used_in_term(names, stmt->assign.lhs);
            names_used_in_term(names, stmt->assign.rhs);
            break;

        case ST_SWAP:
            names_used_in_term(names, stmt->swap.lhs);
            names_used_in_term(names, stmt->swap.rhs);
            break;

        case ST_RETURN:
            names_used_in_term(names, stmt->ret.value);
            break;

        case ST_ASSERT:
            names_used_in_term(names, stmt->assert_data.condition);
            names_used_in_statements(names, stmt->assert_data.proof);
            break;

        case ST_ASSUME:
            names_used_in_term(names, stmt->assume.condition);
            break;

        case ST_IF:
            names_used_in_term(names, stmt->if_data.condition);
            names_used_in_statements(names, stmt->if_data.then_block);
            names_used_in_statements(names, stmt->if_data.else_block);
            break;

        case ST_WHILE:
            names_used_in_term(names, stmt->while_data.condition);
            names_used_in_attributes(names, stmt->while_data.attributes);
            names_used_in_statements(names, stmt->while_data.body);
            break;

        case ST_CALL:
            names_used_in_term(names, stmt->call.term);
            break;

        case ST_MATCH:
            names_used_in_term(names, stmt->match.scrutinee);
            for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {
                names_used_in_pattern(names, arm->pattern);
                names_used_in_statements(names, arm->rhs);
            }
            break;

        case ST_MATCH_FAILURE:
            break;

        case ST_SHOW_HIDE:
            hash_table_insert(names, stmt->show_hide.name, NULL);
            break;
        }

        stmt = stmt->next;
    }
}


//
// Decls
//

void names_used_in_decl(struct HashTable *names, struct Decl *decl)
{
    switch (decl->tag) {
    case DECL_CONST:
        names_used_in_term(names, decl->const_data.rhs);
        break;

    case DECL_FUNCTION:
        for (struct TyVarList *tyvar = decl->function_data.tyvars; tyvar; tyvar = tyvar->next) {
            hash_table_insert(names, tyvar->name, NULL);
        }
        for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
            hash_table_insert(names, arg->name, NULL);
            names_used_in_type(names, arg->type);
        }
        names_used_in_type(names, decl->function_data.return_type);
        names_used_in_attributes(names, decl->attributes);
        names_used_in_statements(names, decl->function_data.body);
        break;

    case DECL_DATATYPE:
        for (struct TyVarList *tyvar = decl->datatype_data.tyvars; tyvar; tyvar = tyvar->next) {
            hash_table_insert(names, tyvar->name, NULL);
        }
        for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
            hash_table_insert(names, ctor->name, NULL);
            names_used_in_type(names, ctor->payload);
        }
        break;

    case DECL_TYPEDEF:
        for (struct TyVarList *tyvar = decl->typedef_data.tyvars; tyvar; tyvar = tyvar->next) {
            hash_table_insert(names, tyvar->name, NULL);
        }
        names_used_in_type(names, decl->typedef_data.rhs);
        break;
    }
}


//
// get_modified_var_names
//

// return the TM_VAR at the root of an lvalue - if one exists.
static const struct Term * get_lvalue_root(const struct Term *lvalue)
{
    switch (lvalue->tag) {
    case TM_VAR:
        return lvalue;

    case TM_FIELD_PROJ:
        return get_lvalue_root(lvalue->field_proj.lhs);

    case TM_ARRAY_PROJ:
        return get_lvalue_root(lvalue->array_proj.lhs);

    default:
        return NULL;
    }
}

static const struct Term * get_lvalue_root_following_refs(const struct HashTable *refs,
                                                          const struct Term *lvalue)
{
    const struct Term * root = get_lvalue_root(lvalue);
    if (!root) fatal_error("couldn't find lvalue from ref arg");
    while (true) {
        // if it is a ref then track back to the referenced variable
        const struct Term *term = hash_table_lookup(refs, root->var.name);
        if (!term) break;
        root = get_lvalue_root(term);
    }
    return root;
}

static void get_modified_vars_from_call(struct HashTable *names,
                                        struct HashTable *refs,
                                        struct Term *term)
{
    if (term->tag == TM_CALL) {
        struct Type *fun_type = term->call.func->type;
        struct FunArg *formal = fun_type->function_data.args;
        struct OpTermList *actual = term->call.args;
        for (; formal; formal = formal->next, actual = actual->next) {
            if (formal->ref) {
                const struct Term * lvalue = get_lvalue_root_following_refs(refs, actual->rhs);
                hash_table_insert(names, lvalue->var.name, lvalue->type);
            }
        }
    }
}

static void get_modified_vars_impl(struct HashTable *names,
                                   struct HashTable *refs,
                                   struct Statement *stmt)
{
    while (stmt) {
        switch (stmt->tag) {
        case ST_VAR_DECL:
            if (stmt->var_decl.ref) {
                // track ref bindings, since vars might be modified
                // indirectly through references
                hash_table_insert(refs, stmt->var_decl.name, stmt->var_decl.rhs);
            }

            // if the term is TM_CALL, vars might have been modified via ref args
            // (note: calls with ref args are not allowed in sub-terms, only the
            // top-level term, so no need to recursively descend into the term.)
            get_modified_vars_from_call(names, refs, stmt->var_decl.rhs);
            break;

        case ST_FIX:
            hash_table_insert(refs, stmt->fix.name, NULL);
            break;

        case ST_OBTAIN:
            hash_table_insert(refs, stmt->obtain.name, NULL);
            break;

        case ST_USE:
            // use doesn't modify anything
            break;

        case ST_ASSIGN:
            {
                const struct Term *root = get_lvalue_root_following_refs(refs, stmt->assign.lhs);
                hash_table_insert(names, root->var.name, root->type);

                // if the rhs is a call term, then further vars might be modified in the call
                get_modified_vars_from_call(names, refs, stmt->assign.rhs);
            }
            break;

        case ST_SWAP:
            {
                const struct Term *lhs_root = get_lvalue_root_following_refs(refs, stmt->swap.lhs);
                hash_table_insert(names, lhs_root->var.name, lhs_root->type);

                const struct Term *rhs_root = get_lvalue_root_following_refs(refs, stmt->swap.rhs);
                hash_table_insert(names, rhs_root->var.name, rhs_root->type);
            }
            break;

        case ST_RETURN:
            break;

        case ST_ASSERT:
            get_modified_vars_impl(names, refs, stmt->assert_data.proof);
            break;

        case ST_ASSUME:
            break;

        case ST_IF:
            get_modified_vars_impl(names, refs, stmt->if_data.then_block);
            get_modified_vars_impl(names, refs, stmt->if_data.else_block);
            break;

        case ST_WHILE:
            get_modified_vars_impl(names, refs, stmt->while_data.body);
            break;

        case ST_CALL:
            {
                // ref args might be modified
                get_modified_vars_from_call(names, refs, stmt->call.term);
            }
            break;

        case ST_MATCH:
            for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {
                if (arm->pattern->tag == PAT_VARIANT
                && arm->pattern->variant.payload->tag == PAT_VAR
                && arm->pattern->variant.payload->var.ref) {
                    // track refs to the scrutinee
                    hash_table_insert(refs, arm->pattern->variant.payload->var.name, stmt->match.scrutinee);
                }
                get_modified_vars_impl(names, refs, arm->rhs);
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

void get_modified_var_names(struct HashTable *names, struct Statement *stmt)
{
    struct HashTable *refs = new_hash_table();
    get_modified_vars_impl(names, refs, stmt);
    free_hash_table(refs);
}
