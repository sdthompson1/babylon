/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "util.h"

#include <stdlib.h>
#include <string.h>


//
// Transform functions
//

void * transform_type_list(struct TypeTransform *tr, void *context, struct TypeList *list)
{
    if (list == NULL) {
        return NULL;
    }

    void * type_result = transform_type(tr, context, list->type);
    void * next_result = transform_type_list(tr, context, list->next);

    if (tr->transform_type_list) {
        return tr->transform_type_list(context, list, type_result, next_result);
    } else {
        return NULL;
    }
}

void * transform_tyvar_list(struct TypeTransform *tr, void *context, struct TyVarList *list)
{
    if (list == NULL) {
        return NULL;
    }

    void * next_result = transform_tyvar_list(tr, context, list->next);

    if (tr->transform_tyvar_list) {
        return tr->transform_tyvar_list(context, list, next_result);
    } else {
        return NULL;
    }
}

void * transform_name_type_list(struct TypeTransform *tr, void *context, struct NameTypeList *list)
{
    if (list == NULL) {
        return NULL;
    }

    void * type_result = transform_type(tr, context, list->type);
    void * next_result = transform_name_type_list(tr, context, list->next);

    if (tr->transform_name_type_list) {
        return tr->transform_name_type_list(context, list, type_result, next_result);
    } else {
        return NULL;
    }
}

void * transform_fun_args(struct TypeTransform *tr, void *context, struct FunArg *fun_args)
{
    if (fun_args == NULL) {
        return NULL;
    }

    void * type_result = transform_type(tr, context, fun_args->type);
    void * next_result = transform_fun_args(tr, context, fun_args->next);

    if (tr->transform_fun_arg) {
        return tr->transform_fun_arg(context, fun_args, type_result, next_result);
    } else {
        return NULL;
    }
}

void * transform_type(struct TypeTransform *tr, void *context, struct Type *type)
{
    if (type == NULL) {
        return NULL;
    }

    switch (type->tag) {
    case TY_VAR:
        if (tr->transform_var) {
            return tr->transform_var(context, type);
        } else {
            return NULL;
        }
        break;

    case TY_BOOL:
        if (tr->transform_bool) {
            return tr->transform_bool(context, type);
        } else {
            return NULL;
        }
        break;

    case TY_FINITE_INT:
        if (tr->transform_finite_int) {
            return tr->transform_finite_int(context, type);
        } else {
            return NULL;
        }
        break;

    case TY_MATH_INT:
        if (tr->transform_math_int) {
            return tr->transform_math_int(context, type);
        } else {
            return NULL;
        }
        break;

    case TY_MATH_REAL:
        if (tr->transform_math_real) {
            return tr->transform_math_real(context, type);
        } else {
            return NULL;
        }
        break;

    case TY_RECORD:
        {
            void * fields_result = transform_name_type_list(tr, context, type->record_data.fields);

            if (tr->transform_record) {
                return tr->transform_record(context, type, fields_result);
            } else {
                return NULL;
            }
        }
        break;

    case TY_VARIANT:
        {
            void * variants_result = transform_name_type_list(tr, context, type->variant_data.variants);

            if (tr->transform_variant) {
                return tr->transform_variant(context, type, variants_result);
            } else {
                return NULL;
            }
        }
        break;

    case TY_ARRAY:
        {
            void * elt_type_result = transform_type(tr, context, type->array_data.element_type);

            if (tr->transform_array) {
                return tr->transform_array(context, type, elt_type_result);
            } else {
                return NULL;
            }
        }
        break;

    case TY_FUNCTION:
        {
            void * args_result = transform_fun_args(tr, context, type->function_data.args);
            void * ret_result = transform_type(tr, context, type->function_data.return_type);

            if (tr->transform_function) {
                return tr->transform_function(context, type, args_result, ret_result);
            } else {
                return NULL;
            }
        }
        break;

    case TY_FORALL:
        {
            void * vars_result = transform_tyvar_list(tr, context, type->forall_data.tyvars);
            void * child_type_result = transform_type(tr, context, type->forall_data.type);

            if (tr->transform_forall) {
                return tr->transform_forall(context, type, vars_result, child_type_result);
            } else {
                return NULL;
            }
        }
        break;

    case TY_LAMBDA:
        {
            void * vars_result = transform_tyvar_list(tr, context, type->lambda_data.tyvars);
            void * child_type_result = transform_type(tr, context, type->lambda_data.type);

            if (tr->transform_lambda) {
                return tr->transform_lambda(context, type, vars_result, child_type_result);
            } else {
                return NULL;
            }
        }
        break;

    case TY_APP:
        {
            void * lhs_result = transform_type(tr, context, type->app_data.lhs);
            void * tyargs_result = transform_type_list(tr, context, type->app_data.tyargs);

            if (tr->transform_app) {
                return tr->transform_app(context, type, lhs_result, tyargs_result);
            } else {
                return NULL;
            }
        }
        break;
    }

    fatal_error("transform_type, bad tag");
}

void * transform_op_term_list(struct TermTransform *tr, void *context, struct OpTermList *list)
{
    if (list == NULL) {
        return NULL;
    }

    void * rhs_result = transform_term(tr, context, list->rhs);
    void * next_result = transform_op_term_list(tr, context, list->next);

    if (tr->transform_op_term_list) {
        return tr->transform_op_term_list(context, list, rhs_result, next_result);
    } else {
        return NULL;
    }
}

void * transform_name_term_list(struct TermTransform *tr, void *context, struct NameTermList *list)
{
    if (list == NULL) {
        return NULL;
    }

    void * term_result = transform_term(tr, context, list->term);
    void * next_result = transform_name_term_list(tr, context, list->next);

    if (tr->transform_name_term_list) {
        return tr->transform_name_term_list(context, list, term_result, next_result);
    } else {
        return NULL;
    }
}

void * transform_arm(struct TermTransform *tr, void *context, struct Arm *arm)
{
    if (arm == NULL) {
        return NULL;
    }

    void * rhs_result = transform_term(tr, context, arm->rhs);
    void * next_result = transform_arm(tr, context, arm->next);

    if (tr->transform_arm) {
        return tr->transform_arm(context, arm, rhs_result, next_result);
    } else {
        return NULL;
    }
}

void * transform_term(struct TermTransform *tr, void *context, struct Term *term)
{
    if (term == NULL) {
        return NULL;
    }

    void *type_result = transform_type(&tr->type_transform, context, term->type);

    switch (term->tag) {
    case TM_VAR:
        {
            if (tr->transform_var) {
                return tr->transform_var(context, term, type_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_DEFAULT:
        if (tr->transform_default) {
            return tr->transform_default(context, term, type_result);
        } else {
            return NULL;
        }
        break;

    case TM_BOOL_LITERAL:
        if (tr->transform_bool_literal) {
            return tr->transform_bool_literal(context, term, type_result);
        } else {
            return NULL;
        }
        break;

    case TM_INT_LITERAL:
        if (tr->transform_int_literal) {
            return tr->transform_int_literal(context, term, type_result);
        } else {
            return NULL;
        }
        break;

    case TM_STRING_LITERAL:
        if (tr->transform_string_literal) {
            return tr->transform_string_literal(context, term, type_result);
        } else {
            return NULL;
        }
        break;

    case TM_ARRAY_LITERAL:
        {
            void *terms_result = transform_op_term_list(tr, context, term->array_literal.terms);
            if (tr->transform_array_literal) {
                return tr->transform_array_literal(context, term, type_result, terms_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_CAST:
        {
            void * target_type_result = transform_type(&tr->type_transform, context, term->cast.target_type);
            void * operand_result = transform_term(tr, context, term->cast.operand);
            if (tr->transform_cast) {
                return tr->transform_cast(context, term, type_result, target_type_result, operand_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_IF:
        if (tr->nr_transform_if) {
            return tr->nr_transform_if(tr, context, term, type_result);
        } else {
            void * cond_result = transform_term(tr, context, term->if_data.cond);
            void * then_result = transform_term(tr, context, term->if_data.then_branch);
            void * else_result = transform_term(tr, context, term->if_data.else_branch);
            if (tr->transform_if) {
                return tr->transform_if(context, term, type_result, cond_result, then_result, else_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_UNOP:
        {
            void * operand_result = transform_term(tr, context, term->unop.operand);
            if (tr->transform_unop) {
                return tr->transform_unop(context, term, type_result, operand_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_BINOP:
        if (tr->nr_transform_binop) {
            return tr->nr_transform_binop(tr, context, term, type_result);
        } else {
            void * lhs_result = transform_term(tr, context, term->binop.lhs);
            void * list_result = transform_op_term_list(tr, context, term->binop.list);
            if (tr->transform_binop) {
                return tr->transform_binop(context, term, type_result, lhs_result, list_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_LET:
        if (tr->nr_transform_let) {
            return tr->nr_transform_let(tr, context, term, type_result);
        } else {
            void * rhs_result = transform_term(tr, context, term->let.rhs);
            void * body_result = transform_term(tr, context, term->let.body);

            if (tr->transform_let) {
                return tr->transform_let(context, term, type_result, rhs_result, body_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_QUANTIFIER:
        if (tr->nr_transform_quantifier) {
            return tr->nr_transform_quantifier(tr, context, term, type_result);
        } else {
            void * var_type_result = transform_type(&tr->type_transform, context, term->quant.type);
            void * body_result = transform_term(tr, context, term->quant.body);
            if (tr->transform_quantifier) {
                return tr->transform_quantifier(context, term, type_result, var_type_result, body_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_CALL:
        if (tr->nr_transform_call) {
            return tr->nr_transform_call(tr, context, term, type_result);
        } else {
            void *func_result = transform_term(tr, context, term->call.func);
            void *args_result = transform_op_term_list(tr, context, term->call.args);
            if (tr->transform_call) {
                return tr->transform_call(context, term, type_result, func_result, args_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_TYAPP:
        if (tr->nr_transform_tyapp) {
            return tr->nr_transform_tyapp(tr, context, term, type_result);
        } else {
            void *lhs_result = transform_term(tr, context, term->tyapp.lhs);
            void *tyargs_result = transform_type_list(&tr->type_transform, context, term->tyapp.tyargs);
            if (tr->transform_tyapp) {
                return tr->transform_tyapp(context, term, type_result, lhs_result, tyargs_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_RECORD:
        {
            void *fields_result = transform_name_term_list(tr, context, term->record.fields);
            if (tr->transform_record) {
                return tr->transform_record(context, term, type_result, fields_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_RECORD_UPDATE:
        {
            void *lhs_result = transform_term(tr, context, term->record_update.lhs);
            void *fields_result = transform_name_term_list(tr, context, term->record_update.fields);
            if (tr->transform_record_update) {
                return tr->transform_record_update(context, term, type_result, lhs_result, fields_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_FIELD_PROJ:
        if (tr->nr_transform_field_proj) {
            return tr->nr_transform_field_proj(tr, context, term, type_result);
        } else {
            void *lhs_result = transform_term(tr, context, term->field_proj.lhs);
            if (tr->transform_field_proj) {
                return tr->transform_field_proj(context, term, type_result, lhs_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_VARIANT:
        {
            void *payload_result = transform_term(tr, context, term->variant.payload);
            if (tr->transform_variant) {
                return tr->transform_variant(context, term, type_result, payload_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_MATCH:
        if (tr->nr_transform_match) {
            return tr->nr_transform_match(tr, context, term, type_result);
        } else {
            void *scrut_result = transform_term(tr, context, term->match.scrutinee);
            void *arm_result = transform_arm(tr, context, term->match.arms);
            if (tr->transform_match) {
                return tr->transform_match(context, term, type_result, scrut_result, arm_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_MATCH_FAILURE:
        if (tr->transform_match_failure) {
            return tr->transform_match_failure(context, term, type_result);
        } else {
            return NULL;
        }
        break;

    case TM_SIZEOF:
        {
            void *rhs_result = transform_term(tr, context, term->sizeof_data.rhs);
            if (tr->transform_sizeof) {
                return tr->transform_sizeof(context, term, type_result, rhs_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_ALLOCATED:
        {
            void *rhs_result = transform_term(tr, context, term->allocated.rhs);
            if (tr->transform_allocated) {
                return tr->transform_allocated(context, term, type_result, rhs_result);
            } else {
                return NULL;
            }
        }
        break;

    case TM_ARRAY_PROJ:
        if (tr->nr_transform_array_proj) {
            return tr->nr_transform_array_proj(tr, context, term, type_result);
        } else {
            void *lhs_result = transform_term(tr, context, term->array_proj.lhs);
            void *index_results = transform_op_term_list(tr, context, term->array_proj.indexes);
            if (tr->transform_array_proj) {
                return tr->transform_array_proj(context, term, type_result, lhs_result, index_results);
            } else {
                return NULL;
            }
        }
        break;
    }

    fatal_error("transform_term, bad tag");
}


//
// Constructors/destructors -- Types
//

struct Type * make_type(struct Location loc, enum TypeTag tag)
{
    struct Type * type = alloc(sizeof(struct Type));
    type->location = loc;
    type->tag = tag;
    return type;
}

struct Type * make_int_type(struct Location loc, bool is_signed, int num_bits)
{
    struct Type * type = make_type(loc, TY_FINITE_INT);
    type->int_data.is_signed = is_signed;
    type->int_data.num_bits = num_bits;
    return type;
}


static void * copy_ty_var(void *context, struct Type *type)
{
    struct Type *result = make_type(type->location, TY_VAR);
    result->var_data.name = copy_string(type->var_data.name);
    return result;
}

static void * copy_ty_bool(void *context, struct Type *type)
{
    return make_type(type->location, TY_BOOL);
}

static void * copy_ty_finite_int(void *context, struct Type *type)
{
    struct Type *result = make_type(type->location, TY_FINITE_INT);
    result->int_data = type->int_data;
    return result;
}

static void * copy_ty_math_int(void *context, struct Type *type)
{
    return make_type(type->location, TY_MATH_INT);
}

static void * copy_ty_math_real(void *context, struct Type *type)
{
    return make_type(type->location, TY_MATH_REAL);
}

static void * copy_ty_record(void *context, struct Type *type, void *field_list)
{
    struct Type *result = make_type(type->location, TY_RECORD);
    result->record_data.fields = field_list;
    return result;
}

static void * copy_ty_variant(void *context, struct Type *type, void *variants_result)
{
    struct Type *result = make_type(type->location, TY_VARIANT);
    result->variant_data.variants = variants_result;
    return result;
}

static void * copy_ty_array(void *context, struct Type *type, void *elt_type_result)
{
    struct Type *result = make_type(type->location, TY_ARRAY);
    result->array_data.element_type = elt_type_result;
    result->array_data.ndim = type->array_data.ndim;
    result->array_data.resizable = type->array_data.resizable;
    if (type->array_data.sizes) {
        result->array_data.sizes = alloc(type->array_data.ndim * sizeof(struct Term *));
        for (int i = 0; i < type->array_data.ndim; ++i) {
            result->array_data.sizes[i] = copy_term(type->array_data.sizes[i]);
        }
    } else {
        result->array_data.sizes = NULL;
    }
    return result;
}

static void * copy_ty_function(void *context, struct Type *type,
                               void *args, void *return_type)
{
    struct Type *result = make_type(type->location, TY_FUNCTION);
    result->function_data.args = args;
    result->function_data.return_type = return_type;
    return result;
}

static void * copy_ty_forall(void *context, struct Type *type,
                             void *tyvars, void *child_type)
{
    struct Type *result = make_type(type->location, TY_FORALL);
    result->forall_data.tyvars = tyvars;
    result->forall_data.type = child_type;
    return result;
}

static void * copy_ty_lambda(void *context, struct Type *type,
                             void *tyvars, void *child_type)
{
    struct Type *result = make_type(type->location, TY_LAMBDA);
    result->lambda_data.tyvars = tyvars;
    result->lambda_data.type = child_type;
    return result;
}

static void * copy_ty_app(void *context, struct Type *type,
                          void *lhs, void *tyargs)
{
    struct Type *result = make_type(type->location, TY_APP);
    result->app_data.lhs = lhs;
    result->app_data.tyargs = tyargs;
    return result;
}

static void * copy_tyvar_list_node(void *context, struct TyVarList *list, void *next)
{
    struct TyVarList *result = alloc(sizeof(struct TyVarList));
    result->name = copy_string(list->name);
    result->next = next;
    return result;
}

static void * copy_ty_list_node(void *context, struct TypeList *list, void *type, void *next)
{
    struct TypeList *result = alloc(sizeof(struct TypeList));
    result->type = type;
    result->next = next;
    return result;
}

static void * copy_field_list_node(void *context, struct NameTypeList *list, void *type, void *next)
{
    struct NameTypeList *result = alloc(sizeof(struct NameTypeList));
    result->name = copy_string(list->name);
    result->type = type;
    result->next = next;
    return result;
}

static void * copy_fun_arg_node(void *context, struct FunArg *list, void *type, void *next)
{
    struct FunArg *result = alloc(sizeof(struct FunArg));
    result->name = list->name ? copy_string(list->name) : NULL;
    result->type = type;
    result->ref = list->ref;
    result->next = next;
    return result;
}

void copying_type_transform(struct TypeTransform *tr)
{
    tr->transform_var = copy_ty_var;
    tr->transform_bool = copy_ty_bool;
    tr->transform_finite_int = copy_ty_finite_int;
    tr->transform_math_int = copy_ty_math_int;
    tr->transform_math_real = copy_ty_math_real;
    tr->transform_record = copy_ty_record;
    tr->transform_variant = copy_ty_variant;
    tr->transform_array = copy_ty_array;
    tr->transform_function = copy_ty_function;
    tr->transform_forall = copy_ty_forall;
    tr->transform_lambda = copy_ty_lambda;
    tr->transform_app = copy_ty_app;
    tr->transform_tyvar_list = copy_tyvar_list_node;
    tr->transform_type_list = copy_ty_list_node;
    tr->transform_fun_arg = copy_fun_arg_node;
    tr->transform_name_type_list = copy_field_list_node;
}

struct Type * copy_type(const struct Type *type)
{
    struct TypeTransform tr = {0};
    copying_type_transform(&tr);
    return transform_type(&tr, NULL, (struct Type*)type);
}

struct TypeList * copy_type_list(const struct TypeList *type_list)
{
    struct TypeTransform tr = {0};
    copying_type_transform(&tr);
    return transform_type_list(&tr, NULL, (struct TypeList*)type_list);
}

struct TyVarList * copy_tyvar_list(const struct TyVarList *list)
{
    struct TypeTransform tr = {0};
    copying_type_transform(&tr);
    return transform_tyvar_list(&tr, NULL, (struct TyVarList*)list);
}


static void* free_type_0(void *context, struct Type *type)
{
    free(type);
    return NULL;
}

static void* free_type_1(void *context, struct Type *type, void *arg1)
{
    free(type);
    return NULL;
}

static void* free_type_2(void *context, struct Type *type, void *arg1, void *arg2)
{
    free(type);
    return NULL;
}

static void* free_var_type(void *context, struct Type *type)
{
    free((char*)type->var_data.name);
    free(type);
    return NULL;
}

static void* free_array_type(void *context, struct Type *type, void *elt_type_result)
{
    if (type->array_data.sizes) {
        for (int i = 0; i < type->array_data.ndim; ++i) {
            free_term(type->array_data.sizes[i]);
        }
        free(type->array_data.sizes);
    }
    free(type);
    return NULL;
}

static void * free_tyvar_list_node(void *context, struct TyVarList *node, void *next_result)
{
    free((char*)node->name);
    free(node);
    return NULL;
}

static void * free_type_list_node(void *context, struct TypeList *node, void *type_result, void *next_result)
{
    free(node);
    return NULL;
}

static void * free_name_type_list_node(void *context, struct NameTypeList *node, void *type_result, void *next_result)
{
    free((char*)node->name);
    free(node);
    return NULL;
}

static void * free_fun_arg_node(void *context, struct FunArg *node, void *type_result, void *next_result)
{
    free((char*)node->name);
    free(node);
    return NULL;
}

static void freeing_type_transform(struct TypeTransform *tr)
{
    tr->transform_var = free_var_type;
    tr->transform_bool = free_type_0;
    tr->transform_finite_int = free_type_0;
    tr->transform_math_int = free_type_0;
    tr->transform_math_real = free_type_0;
    tr->transform_record = free_type_1;
    tr->transform_variant = free_type_1;
    tr->transform_array = free_array_type;
    tr->transform_function = free_type_2;
    tr->transform_forall = free_type_2;
    tr->transform_lambda = free_type_2;
    tr->transform_app = free_type_2;
    tr->transform_tyvar_list = free_tyvar_list_node;
    tr->transform_type_list = free_type_list_node;
    tr->transform_fun_arg = free_fun_arg_node;
    tr->transform_name_type_list = free_name_type_list_node;
}

void free_type(struct Type *type)
{
    struct TypeTransform tr;
    freeing_type_transform(&tr);
    transform_type(&tr, NULL, type);
}

void free_tyvar_list(struct TyVarList *tyvars)
{
    struct TypeTransform tr;
    freeing_type_transform(&tr);
    transform_tyvar_list(&tr, NULL, tyvars);
}

void free_type_list(struct TypeList *types)
{
    struct TypeTransform tr;
    freeing_type_transform(&tr);
    transform_type_list(&tr, NULL, types);
}

void free_name_type_list(struct NameTypeList *list)
{
    struct TypeTransform tr;
    freeing_type_transform(&tr);
    transform_name_type_list(&tr, NULL, list);
}


//
// Constructors/destructors -- Patterns
//

struct Pattern * make_pattern(struct Location loc, enum PatternTag tag)
{
    struct Pattern * result = alloc(sizeof(struct Pattern));
    result->location = loc;
    result->tag = tag;
    return result;
}

static struct NamePatternList * copy_name_pattern_list(struct NamePatternList *input)
{
    if (input) {
        struct NamePatternList *result = alloc(sizeof(struct NamePatternList));
        result->name = input->name ? copy_string(input->name) : NULL;
        result->pattern = copy_pattern(input->pattern);
        result->next = copy_name_pattern_list(input->next);
        return result;
    } else {
        return NULL;
    }
}

struct Pattern * copy_pattern(const struct Pattern *input)
{
    if (input == NULL) return NULL;

    struct Pattern *output = alloc(sizeof(struct Pattern));
    output->location = input->location;
    output->tag = input->tag;

    switch (input->tag) {
    case PAT_VAR:
        output->var.name = copy_string(input->var.name);
        output->var.ref = input->var.ref;
        break;

    case PAT_BOOL:
        output->bool_data.value = input->bool_data.value;
        break;

    case PAT_INT:
        output->int_data.data = copy_string(input->int_data.data);
        break;

    case PAT_RECORD:
        output->record.fields = copy_name_pattern_list(input->record.fields);
        break;

    case PAT_VARIANT:
        output->variant.variant_name = copy_string(input->variant.variant_name);
        output->variant.payload = copy_pattern(input->variant.payload);
        break;

    case PAT_WILDCARD:
        break;
    }

    return output;
}

void free_name_pattern_list(struct NamePatternList *list)
{
    while (list) {
        struct NamePatternList *next = list->next;
        free((void*)list->name);
        free_pattern(list->pattern);
        free(list);
        list = next;
    }
}

void free_pattern(struct Pattern *pattern)
{
    if (pattern) {
        switch (pattern->tag) {
        case PAT_VAR:
            free((void*)pattern->var.name);
            break;

        case PAT_BOOL:
            break;

        case PAT_INT:
            free((void*)pattern->int_data.data);
            break;

        case PAT_RECORD:
            free_name_pattern_list(pattern->record.fields);
            break;

        case PAT_VARIANT:
            free((char*)pattern->variant.variant_name);
            free_pattern(pattern->variant.payload);
            break;

        case PAT_WILDCARD:
            break;
        }

        free(pattern);
    }
}


//
// Constructors/destructors -- Terms
//

struct Term * make_term(struct Location loc, enum TermTag tag)
{
    struct Term *result = alloc(sizeof(struct Term));
    result->location = loc;
    result->type = NULL;
    result->tag = tag;
    return result;
}

struct Term * make_bool_literal_term(struct Location loc, bool value)
{
    struct Term * result = make_term(loc, TM_BOOL_LITERAL);
    result->bool_literal.value = value;
    return result;
}

struct Term * make_int_literal_term(struct Location loc, const char *data)
{
    struct Term * result = make_term(loc, TM_INT_LITERAL);
    result->int_literal.data = copy_string(data);
    return result;
}

struct Term * make_string_literal_term(struct Location loc, const uint8_t *data, uint32_t length)
{
    struct Term * result = make_term(loc, TM_STRING_LITERAL);
    uint8_t *new_data = alloc(length);
    if (length != 0) memcpy(new_data, data, length);
    result->string_literal.data = new_data;
    result->string_literal.length = length;
    return result;
}

struct Term * make_var_term(struct Location loc, const char *name)
{
    struct Term * result = make_term(loc, TM_VAR);
    result->var.name = copy_string(name);
    result->var.postcond_new = false;
    return result;
}


static void* copy_var_term(void *context, struct Term *term, void *type_result)
{
    struct Term *result = make_term(term->location, TM_VAR);
    result->type = type_result;
    result->var.name = copy_string(term->var.name);
    result->var.postcond_new = term->var.postcond_new;
    return result;
}

static void* copy_default_term(void *context, struct Term *term, void *type_result)
{
    struct Term *result = make_term(term->location, TM_DEFAULT);
    result->type = type_result;
    return result;
}

static void* copy_bool_literal_term(void *context, struct Term *term, void *type_result)
{
    struct Term *result = make_term(term->location, TM_BOOL_LITERAL);
    result->type = type_result;
    result->bool_literal.value = term->bool_literal.value;
    return result;
}

static void* copy_int_literal_term(void *context, struct Term *term, void *type_result)
{
    struct Term *result = make_term(term->location, TM_INT_LITERAL);
    result->type = type_result;
    result->int_literal.data = copy_string(term->int_literal.data);
    return result;
}

static void* copy_string_literal_term(void *context, struct Term *term, void *type_result)
{
    struct Term *result = make_term(term->location, TM_STRING_LITERAL);
    result->type = type_result;

    uint32_t length = term->string_literal.length;
    const void *old_data = term->string_literal.data;
    void *new_data = alloc(length);
    memcpy(new_data, old_data, length);
    result->string_literal.data = new_data;
    result->string_literal.length = length;

    return result;
}

static void* copy_array_literal_term(void *context, struct Term *term, void *type_result, void *list_result)
{
    struct Term *result = make_term(term->location, TM_ARRAY_LITERAL);
    result->type = type_result;
    result->array_literal.terms = list_result;
    return result;
}

static void* copy_cast_term(void *context, struct Term *term, void *type_result, void *target_type_result, void *operand_result)
{
    struct Term *result = make_term(term->location, TM_CAST);
    result->type = type_result;
    result->cast.target_type = target_type_result;
    result->cast.operand = operand_result;
    return result;
}

static void* copy_if_term(void *context, struct Term *term, void *type_result, void *cond_result, void *then_result, void *else_result)
{
    struct Term *result = make_term(term->location, TM_IF);
    result->type = type_result;
    result->if_data.cond = cond_result;
    result->if_data.then_branch = then_result;
    result->if_data.else_branch = else_result;
    return result;
}

static void* copy_unop_term(void *context, struct Term *term, void *type_result, void *operand_result)
{
    struct Term *result = make_term(term->location, TM_UNOP);
    result->type = type_result;
    result->unop.operator = term->unop.operator;
    result->unop.operand = operand_result;
    return result;
}

static void* copy_binop_term(void *context, struct Term *term, void *type_result, void *lhs_result, void *list_result)
{
    struct Term *result = make_term(term->location, TM_BINOP);
    result->type = type_result;
    result->binop.lhs = lhs_result;
    result->binop.list = list_result;
    return result;
}

static void* copy_let_term(void *context, struct Term *term, void *type_result, void *rhs_result, void *body_result)
{
    struct Term *result = make_term(term->location, TM_LET);
    result->type = type_result;
    result->let.name = copy_string(term->let.name);
    result->let.rhs = rhs_result;
    result->let.body = body_result;
    return result;
}

static void* copy_quantifier_term(void *context, struct Term *term, void *type_result, void *var_type_result, void *body_result)
{
    struct Term *result = make_term(term->location, TM_QUANTIFIER);
    result->type = type_result;
    result->quant.quant = term->quant.quant;
    result->quant.name = copy_string(term->quant.name);
    result->quant.type = var_type_result;
    result->quant.body = body_result;
    return result;
}

static void* copy_call_term(void *context, struct Term *term, void *type_result, void *func_result, void *args_result)
{
    struct Term *result = make_term(term->location, TM_CALL);
    result->type = type_result;
    result->call.func = func_result;
    result->call.args = args_result;
    return result;
}

static void* copy_tyapp_term(void *context, struct Term *term, void *type_result, void *lhs_result, void *tyargs_result)
{
    struct Term *result = make_term(term->location, TM_TYAPP);
    result->type = type_result;
    result->tyapp.lhs = lhs_result;
    result->tyapp.tyargs = tyargs_result;
    return result;
}

static void* copy_record_term(void *context, struct Term *term, void *type_result, void *fields_result)
{
    struct Term *result = make_term(term->location, TM_RECORD);
    result->type = type_result;
    result->record.fields = fields_result;
    return result;
}

static void* copy_record_update_term(void *context, struct Term *term, void *type_result, void *lhs_result, void *fields_result)
{
    struct Term *result = make_term(term->location, TM_RECORD_UPDATE);
    result->type = type_result;
    result->record_update.lhs = lhs_result;
    result->record_update.fields = fields_result;
    return result;
}

static void* copy_field_proj_term(void *context, struct Term *term, void *type_result, void *lhs_result)
{
    struct Term *result = make_term(term->location, TM_FIELD_PROJ);
    result->type = type_result;
    result->field_proj.lhs = lhs_result;
    result->field_proj.field_name = copy_string(term->field_proj.field_name);
    return result;
}

static void* copy_variant_term(void *context, struct Term *term, void *type_result, void *payload_result)
{
    struct Term *result = make_term(term->location, TM_VARIANT);
    result->type = type_result;
    result->variant.variant_name = copy_string(term->variant.variant_name);
    result->variant.payload = payload_result;
    return result;
}

static void* copy_match_term(void *context, struct Term *term, void *type_result, void *scrut_result, void *arm_result)
{
    struct Term *result = make_term(term->location, TM_MATCH);
    result->type = type_result;
    result->match.scrutinee = scrut_result;
    result->match.arms = arm_result;
    return result;
}

static void* copy_match_failure_term(void *context, struct Term *term, void *type_result)
{
    struct Term *result = make_term(term->location, TM_MATCH_FAILURE);
    result->type = type_result;
    return result;
}

static void* copy_sizeof_term(void *context, struct Term *term, void *type_result, void *rhs_result)
{
    struct Term *result = make_term(term->location, TM_SIZEOF);
    result->type = type_result;
    result->sizeof_data.rhs = rhs_result;
    return result;
}

static void* copy_allocated_term(void *context, struct Term *term, void *type_result, void *rhs_result)
{
    struct Term *result = make_term(term->location, TM_ALLOCATED);
    result->type = type_result;
    result->allocated.rhs = rhs_result;
    return result;
}

static void* copy_array_proj_term(void *context, struct Term *term, void *type_result, void *lhs_result, void *index_results)
{
    struct Term *result = make_term(term->location, TM_ARRAY_PROJ);
    result->type = type_result;
    result->array_proj.lhs = lhs_result;
    result->array_proj.indexes = index_results;
    return result;
}

static void* copy_op_term_list(void *context, struct OpTermList *op_term_list, void *rhs_result, void *next_result)
{
    struct OpTermList *result = alloc(sizeof(struct OpTermList));
    result->operator = op_term_list->operator;
    result->rhs = rhs_result;
    result->next = next_result;
    return result;
}

static void* copy_name_term_list(void *context, struct NameTermList *name_term_list, void *term_result, void *next_result)
{
    struct NameTermList *result = alloc(sizeof(struct NameTermList));
    result->location = name_term_list->location;
    result->name = copy_string(name_term_list->name);
    result->term = term_result;
    result->next = next_result;
    return result;
}

static void* copy_arm(void *context, struct Arm *arm, void *rhs_result, void *next_result)
{
    struct Arm *result = alloc(sizeof(struct Arm));
    result->location = arm->location;
    result->pattern = copy_pattern(arm->pattern);
    result->rhs = rhs_result;
    result->next = next_result;
    return result;
}

static void copying_term_transform(struct TermTransform *tr)
{
    tr->transform_var = copy_var_term;
    tr->transform_default = copy_default_term;
    tr->transform_bool_literal = copy_bool_literal_term;
    tr->transform_int_literal = copy_int_literal_term;
    tr->transform_string_literal = copy_string_literal_term;
    tr->transform_array_literal = copy_array_literal_term;
    tr->transform_cast = copy_cast_term;
    tr->transform_if = copy_if_term;
    tr->transform_unop = copy_unop_term;
    tr->transform_binop = copy_binop_term;
    tr->transform_let = copy_let_term;
    tr->transform_quantifier = copy_quantifier_term;
    tr->transform_call = copy_call_term;
    tr->transform_tyapp = copy_tyapp_term;
    tr->transform_record = copy_record_term;
    tr->transform_record_update = copy_record_update_term;
    tr->transform_field_proj = copy_field_proj_term;
    tr->transform_variant = copy_variant_term;
    tr->transform_match = copy_match_term;
    tr->transform_match_failure = copy_match_failure_term;
    tr->transform_sizeof = copy_sizeof_term;
    tr->transform_allocated = copy_allocated_term;
    tr->transform_array_proj = copy_array_proj_term;
    tr->transform_op_term_list = copy_op_term_list;
    tr->transform_name_term_list = copy_name_term_list;
    tr->transform_arm = copy_arm;
    copying_type_transform(&tr->type_transform);
}

struct Term *copy_term(const struct Term *term)
{
    struct TermTransform tr = {0};
    copying_term_transform(&tr);
    return transform_term(&tr, NULL, (struct Term*)term);
}


static void* free_term_0(void *context, struct Term *term, void *type_result)
{
    free(term);
    return NULL;
}

static void* free_term_1(void *context, struct Term *term, void *type_result, void *result1)
{
    free(term);
    return NULL;
}

static void* free_term_2(void *context, struct Term *term, void *type_result, void *result1, void *result2)
{
    free(term);
    return NULL;
}

static void* free_term_3(void *context, struct Term *term, void *type_result, void *result1, void *result2, void *result3)
{
    free(term);
    return NULL;
}

static void* free_var_term(void *context, struct Term *term, void *type_result)
{
    free((void*)term->var.name);
    free(term);
    return NULL;
}

static void* free_int_literal_term(void *context, struct Term *term, void *type_result)
{
    free((void*)term->int_literal.data);
    free(term);
    return NULL;
}

static void* free_string_literal_term(void *context, struct Term *term, void *type_result)
{
    free((void*)term->string_literal.data);
    free(term);
    return NULL;
}

static void* free_let_term(void *context, struct Term *term, void *type_result, void *result1, void *result2)
{
    free((void*)term->let.name);
    free(term);
    return NULL;
}

static void* free_quantifier_term(void *context, struct Term *term, void *type_result, void *result1, void *result2)
{
    free((void*)term->quant.name);
    free(term);
    return NULL;
}

static void* free_field_proj_term(void *context, struct Term *term, void *type_result, void *result1)
{
    free((void*)term->field_proj.field_name);
    free(term);
    return NULL;
}

static void* free_variant_term(void *context, struct Term *term, void *type_result, void *payload_result)
{
    free((void*)term->variant.variant_name);
    free(term);
    return NULL;
}

static void* free_op_term_list_node(void *context, struct OpTermList *list, void *rhs_result, void *next_result)
{
    free(list);
    return NULL;
}

static void* free_name_term_list_node(void *context, struct NameTermList *list, void *term_result, void *next_result)
{
    free((void*)list->name);
    free(list);
    return NULL;
}

static void* free_arm_node(void *context, struct Arm *arm, void *rhs_result, void *next_result)
{
    free_pattern(arm->pattern);
    free(arm);
    return NULL;
}

static void freeing_term_transform(struct TermTransform *tr)
{
    tr->transform_var = free_var_term;
    tr->transform_default = free_term_0;
    tr->transform_bool_literal = free_term_0;
    tr->transform_int_literal = free_int_literal_term;
    tr->transform_string_literal = free_string_literal_term;
    tr->transform_array_literal = free_term_1;
    tr->transform_cast = free_term_2;
    tr->transform_if = free_term_3;
    tr->transform_unop = free_term_1;
    tr->transform_binop = free_term_2;
    tr->transform_let = free_let_term;
    tr->transform_quantifier = free_quantifier_term;
    tr->transform_call = free_term_2;
    tr->transform_tyapp = free_term_2;
    tr->transform_record = free_term_1;
    tr->transform_record_update = free_term_2;
    tr->transform_field_proj = free_field_proj_term;
    tr->transform_variant = free_variant_term;
    tr->transform_match = free_term_2;
    tr->transform_match_failure = free_term_0;
    tr->transform_sizeof = free_term_1;
    tr->transform_allocated = free_term_1;
    tr->transform_array_proj = free_term_2;
    tr->transform_op_term_list = free_op_term_list_node;
    tr->transform_name_term_list = free_name_term_list_node;
    tr->transform_arm = free_arm_node;
    freeing_type_transform(&tr->type_transform);
}

void free_term(struct Term *term)
{
    struct TermTransform tr = {0};
    freeing_term_transform(&tr);
    transform_term(&tr, NULL, term);
}

void free_name_term_list(struct NameTermList *list)
{
    struct TermTransform tr = {0};
    freeing_term_transform(&tr);
    transform_name_term_list(&tr, NULL, list);
}

void free_op_term_list(struct OpTermList *list)
{
    struct TermTransform tr = {0};
    freeing_term_transform(&tr);
    transform_op_term_list(&tr, NULL, list);
}


//
// Constructors/Destructors -- Other
//

struct Statement * make_statement(struct Location loc, enum StmtTag tag)
{
    struct Statement *result = alloc(sizeof(struct Statement));
    result->location = loc;
    result->next = NULL;
    result->tag = tag;
    result->ghost = false;
    return result;
}

struct Statement * copy_statement(struct Statement *stmt)
{
    if (!stmt) return NULL;

    struct Statement *result = alloc(sizeof(struct Statement));
    result->location = stmt->location;
    result->next = copy_statement(stmt->next);
    result->tag = stmt->tag;

    switch (stmt->tag) {
    case ST_VAR_DECL:
        result->var_decl.name = copy_string(stmt->var_decl.name);
        result->var_decl.type = copy_type(stmt->var_decl.type);
        result->var_decl.rhs = copy_term(stmt->var_decl.rhs);
        result->var_decl.ref = stmt->var_decl.ref;
        break;

    case ST_FIX:
        result->fix.name = copy_string(stmt->fix.name);
        result->fix.type = copy_type(stmt->fix.type);
        break;

    case ST_OBTAIN:
        result->obtain.name = copy_string(stmt->obtain.name);
        result->obtain.type = copy_type(stmt->obtain.type);
        result->obtain.condition = copy_term(stmt->obtain.condition);
        break;

    case ST_USE:
        result->use.term = copy_term(stmt->use.term);
        break;

    case ST_ASSIGN:
        result->assign.lhs = copy_term(stmt->assign.lhs);
        result->assign.rhs = copy_term(stmt->assign.rhs);
        break;

    case ST_SWAP:
        result->swap.lhs = copy_term(stmt->swap.lhs);
        result->swap.rhs = copy_term(stmt->swap.rhs);
        break;

    case ST_RETURN:
        result->ret.value = copy_term(stmt->ret.value);
        break;

    case ST_ASSERT:
        result->assert_data.condition = copy_term(stmt->assert_data.condition);
        result->assert_data.proof = copy_statement(stmt->assert_data.proof);
        break;

    case ST_ASSUME:
        result->assume.condition = copy_term(stmt->assume.condition);
        break;

    case ST_IF:
        result->if_data.condition = copy_term(stmt->if_data.condition);
        result->if_data.then_block = copy_statement(stmt->if_data.then_block);
        result->if_data.else_block = copy_statement(stmt->if_data.else_block);
        break;

    case ST_WHILE:
        result->while_data.condition = copy_term(stmt->while_data.condition);
        result->while_data.attributes = copy_attributes(stmt->while_data.attributes);
        result->while_data.body = copy_statement(stmt->while_data.body);
        break;

    case ST_CALL:
        result->call.term = copy_term(stmt->call.term);
        break;

    case ST_MATCH:
        result->match.scrutinee = copy_term(stmt->match.scrutinee);
        {
            result->match.arms = NULL;
            struct Arm **tail = &result->match.arms;
            for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {
                (*tail) = alloc(sizeof(struct Arm));
                (*tail)->location = arm->location;
                (*tail)->pattern = copy_pattern(arm->pattern);
                (*tail)->rhs = copy_statement(arm->rhs);
                (*tail)->next = NULL;
                tail = &(*tail)->next;
            }
        }
        break;

    case ST_MATCH_FAILURE:
        break;

    case ST_SHOW_HIDE:
        result->show_hide.name = copy_string(stmt->show_hide.name);
        result->show_hide.show = stmt->show_hide.show;
        break;
    }

    result->ghost = stmt->ghost;

    return result;
}

struct Attribute * copy_attributes(struct Attribute *attr)
{
    if (!attr) return NULL;

    struct Attribute *result = alloc(sizeof(struct Attribute));
    result->location = attr->location;
    result->tag = attr->tag;

    switch (attr->tag) {
    case ATTR_REQUIRES:
    case ATTR_ENSURES:
    case ATTR_INVARIANT:
    case ATTR_DECREASES:
        result->term = copy_term(attr->term);
        break;
    }

    result->next = copy_attributes(attr->next);

    return result;
}

void free_statement(struct Statement *stmt)
{
    while (stmt) {
        switch (stmt->tag) {
        case ST_VAR_DECL:
            free((char*)stmt->var_decl.name);
            free_type(stmt->var_decl.type);
            free_term(stmt->var_decl.rhs);
            break;

        case ST_FIX:
            free((char*)stmt->fix.name);
            free_type(stmt->fix.type);
            break;

        case ST_OBTAIN:
            free((char*)stmt->obtain.name);
            free_type(stmt->obtain.type);
            free_term(stmt->obtain.condition);
            break;

        case ST_USE:
            free_term(stmt->use.term);
            break;

        case ST_ASSIGN:
            free_term(stmt->assign.lhs);
            free_term(stmt->assign.rhs);
            break;

        case ST_SWAP:
            free_term(stmt->swap.lhs);
            free_term(stmt->swap.rhs);
            break;

        case ST_RETURN:
            free_term(stmt->ret.value);
            break;

        case ST_ASSERT:
            free_term(stmt->assert_data.condition);
            free_statement(stmt->assert_data.proof);
            break;

        case ST_ASSUME:
            free_term(stmt->assume.condition);
            break;

        case ST_IF:
            free_term(stmt->if_data.condition);
            free_statement(stmt->if_data.then_block);
            free_statement(stmt->if_data.else_block);
            break;

        case ST_WHILE:
            free_term(stmt->while_data.condition);
            free_attributes(stmt->while_data.attributes);
            free_statement(stmt->while_data.body);
            break;

        case ST_CALL:
            free_term(stmt->call.term);
            break;

        case ST_MATCH:
            free_term(stmt->match.scrutinee);
            while (stmt->match.arms) {
                free_pattern(stmt->match.arms->pattern);
                free_statement(stmt->match.arms->rhs);
                struct Arm *next = stmt->match.arms->next;
                free(stmt->match.arms);
                stmt->match.arms = next;
            }
            break;

        case ST_MATCH_FAILURE:
            break;

        case ST_SHOW_HIDE:
            free((void*)stmt->show_hide.name);
            break;
        }

        struct Statement *to_free = stmt;
        stmt = stmt->next;
        free(to_free);
    }
}

void free_fun_arg(struct FunArg *arg)
{
    while (arg) {
        free((char*)arg->name);
        free_type(arg->type);
        struct FunArg *to_free = arg;
        arg = arg->next;
        free(to_free);
    }
}

void free_attributes(struct Attribute *attr)
{
    while (attr) {
        switch (attr->tag) {
        case ATTR_REQUIRES:
        case ATTR_ENSURES:
        case ATTR_INVARIANT:
        case ATTR_DECREASES:
            free_term(attr->term);
            break;
        }

        struct Attribute *to_free = attr;
        attr = attr->next;
        free(to_free);
    }
}

static void free_data_ctors(struct DataCtor *ctor)
{
    while (ctor) {
        free((char*)ctor->name);
        free_type(ctor->payload);
        struct DataCtor *to_free = ctor;
        ctor = ctor->next;
        free(to_free);
    }
}

void free_decl(struct Decl *decl)
{
    while (decl != NULL) {
        free((void*)decl->name);

        switch (decl->tag) {
        case DECL_CONST:
            free_type(decl->const_data.type);
            free_term(decl->const_data.rhs);
            free_term(decl->const_data.value);
            break;

        case DECL_FUNCTION:
            free_tyvar_list(decl->function_data.tyvars);
            free_fun_arg(decl->function_data.args);
            free_type(decl->function_data.return_type);
            free_statement(decl->function_data.body);
            break;

        case DECL_DATATYPE:
            free_tyvar_list(decl->datatype_data.tyvars);
            free_data_ctors(decl->datatype_data.ctors);
            break;

        case DECL_TYPEDEF:
            free_tyvar_list(decl->typedef_data.tyvars);
            free_type(decl->typedef_data.rhs);
            break;
        }

        free_attributes(decl->attributes);
        free_name_list(decl->dependency_names);

        struct Decl *to_free = decl;
        decl = decl->next;
        free(to_free);
    }
}

void free_import(struct Import *import)
{
    while (import) {
        free((void*)import->module_name);
        free((void*)import->alias_name);
        struct Import *to_free = import;
        import = import->next;
        free(to_free);
    }
}

void free_decl_group(struct DeclGroup *decl_group)
{
    while (decl_group) {
        free_decl(decl_group->decl);
        struct DeclGroup *to_free = decl_group;
        decl_group = decl_group->next;
        free(to_free);
    }
}

void free_module(struct Module *module)
{
    if (module != NULL) {
        free((void*)module->name);
        free_import(module->interface_imports);
        free_decl_group(module->interface);
        free_import(module->implementation_imports);
        free_decl_group(module->implementation);
        free(module);
    }
}


//
// Equality testing
//

bool type_lists_equal(const struct TypeList *lhs, const struct TypeList *rhs)
{
    while (lhs != NULL && rhs != NULL) {
        if (!types_equal(lhs->type, rhs->type)) {
            return false;
        }
        lhs = lhs->next;
        rhs = rhs->next;
    }

    return (lhs == NULL && rhs == NULL);
}

bool name_type_lists_equal(const struct NameTypeList *lhs, const struct NameTypeList *rhs)
{
    while (lhs != NULL && rhs != NULL) {

        if (lhs->name == NULL) {
            if (rhs->name != NULL) return false;
        } else {
            if (rhs->name == NULL) return false;
            if (strcmp(lhs->name, rhs->name) != 0) return false;
        }

        // some of the types in the list might be NULL
        // (at least until after typechecking)
        if (lhs->type == NULL && rhs->type != NULL) return false;
        if (lhs->type != NULL && rhs->type == NULL) return false;

        if (lhs->type != NULL && rhs->type != NULL
            && !types_equal(lhs->type, rhs->type)) return false;

        lhs = lhs->next;
        rhs = rhs->next;
    }

    return (lhs == NULL && rhs == NULL);
}

bool funarg_lists_equal(const struct FunArg *lhs, const struct FunArg *rhs)
{
    while (lhs != NULL && rhs != NULL) {

        // note: names ignored

        if (!types_equal(lhs->type, rhs->type)) return false;
        if (lhs->ref != rhs->ref) return false;

        lhs = lhs->next;
        rhs = rhs->next;
    }

    return (lhs == NULL && rhs == NULL);
}

static bool array_size_terms_equal(struct Term **lhs, struct Term **rhs, int ndim)
{
    if (lhs == NULL) {
        return rhs == NULL;

    } else {
        // lhs != NULL
        if (rhs == NULL) {
            return false;
        }

        // both lhs and rhs non-NULL
        for (int i = 0; i < ndim; ++i) {
            if (lhs[i]->tag != TM_INT_LITERAL || rhs[i]->tag != TM_INT_LITERAL) {
                fatal_error("can't compare array types, sizes have not been normalised to TM_INT_LITERAL");
            }
            if (strcmp(lhs[i]->int_literal.data, rhs[i]->int_literal.data) != 0) {
                return false;
            }
        }

        return true;
    }
}

bool types_equal(const struct Type *lhs, const struct Type *rhs)
{
    if (lhs->tag != rhs->tag) {
        return false;
    }

    switch (lhs->tag) {
    case TY_BOOL:
        return true;

    case TY_FINITE_INT:
        return lhs->int_data.is_signed == rhs->int_data.is_signed &&
            lhs->int_data.num_bits == rhs->int_data.num_bits;

    case TY_MATH_INT:
    case TY_MATH_REAL:
        return true;

    case TY_RECORD:
        return name_type_lists_equal(lhs->record_data.fields, rhs->record_data.fields);

    case TY_VARIANT:
        return name_type_lists_equal(lhs->variant_data.variants, rhs->variant_data.variants);

    case TY_ARRAY:
        return lhs->array_data.ndim == rhs->array_data.ndim
            && lhs->array_data.resizable == rhs->array_data.resizable
            && array_size_terms_equal(lhs->array_data.sizes, rhs->array_data.sizes, lhs->array_data.ndim)
            && types_equal(lhs->array_data.element_type, rhs->array_data.element_type);

    case TY_FUNCTION:
        {
            struct Type *lhs_ret = lhs->function_data.return_type;
            struct Type *rhs_ret = rhs->function_data.return_type;
            if (lhs_ret == NULL && rhs_ret != NULL) return false;
            if (lhs_ret != NULL && rhs_ret == NULL) return false;
            if (lhs_ret && !types_equal(lhs_ret, rhs_ret)) return false;

            return funarg_lists_equal(lhs->function_data.args, rhs->function_data.args);
        }

    case TY_FORALL:
    case TY_LAMBDA:
        // error for now
        fatal_error("types_equal: not implemented for TY_FUNCTION, TY_FORALL, TY_LAMBDA");

    case TY_VAR:
        return strcmp(lhs->var_data.name, rhs->var_data.name) == 0;

    case TY_APP:
        return types_equal(lhs->app_data.lhs, rhs->app_data.lhs)
            && type_lists_equal(lhs->app_data.tyargs, rhs->app_data.tyargs);
    }

    fatal_error("types_equal, unknown tag");
}

int tyvar_list_length(const struct TyVarList *list)
{
    int len = 0;
    while (list) {
        ++len;
        list = list->next;
    }
    return len;
}

int type_list_length(const struct TypeList *list)
{
    int len = 0;
    while (list) {
        ++len;
        list = list->next;
    }
    return len;
}
