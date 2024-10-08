/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "eval_const.h"
#include "normal_form.h"
#include "stacked_hash_table.h"
#include "util.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static struct Term * eval_var(TypeEnv *env, struct Term *term)
{
    struct TypeEnvEntry *entry = type_env_lookup(env, term->var.name);
    if (entry && entry->value) {
        return copy_term(entry->value);
    } else {
        report_non_compile_time_constant(term->location);
        return NULL;
    }
}

static struct Term * eval_cast(TypeEnv *env, struct Term *term)
{
    struct Term *operand = eval_to_normal_form(env, term->cast.operand);
    if (!operand) return NULL;

    // Casting to array is allowed, but the operand must be TM_STRING_LITERAL
    // or TM_ARRAY_LITERAL, and the target type must be T[]
    if (term->type->tag == TY_ARRAY) {
        if ((operand->tag != TM_STRING_LITERAL && operand->tag != TM_ARRAY_LITERAL)
        || term->type->array_data.sizes
        || term->type->array_data.resizable) {
            report_non_compile_time_constant(term->location);
            return NULL;
        }
        struct Term *result = make_term(operand->location, TM_CAST);
        result->type = copy_type(term->type);
        result->cast.target_type = copy_type(term->type);
        result->cast.operand = operand;
        return result;
    }

    // Otherwise, the cast must be between different TY_FINITE_INT types
    // (in this function we assume that TY_MATH_INT does not occur).
    if (operand->type->tag != TY_FINITE_INT || term->type->tag != TY_FINITE_INT) {
        fatal_error("eval_cast: types are not as expected");
    }

    // Evaluate the operand to uint64 (either signed or unsigned as
    // appropriate for the type)
    uint64_t value = normal_form_to_int(operand);

    // If casting unsigned to signed, or vice versa, then we need bit
    // 63 clear, otherwise it is an overflow.
    bool valid = true;
    if (term->type->int_data.is_signed != operand->type->int_data.is_signed &&
        (((value + 0u) & UINT64_C(0x8000000000000000)) != 0)) {
        valid = false;
    }
    // Also if the value is out of range for the new type then it is
    // an overflow.
    if (!is_value_in_range_for_type(term->type, value)) {
        valid = false;
    }

    free_term(operand);
    operand = NULL;

    if (!valid) {
        report_compile_time_overflow(term->location);
        return NULL;
    }

    // Return the same value, but in the new type.
    return make_literal_of_type(term->type, value);
}

static struct Term * eval_if(TypeEnv *env, struct Term *term)
{
    struct Term *condition = eval_to_normal_form(env, term->if_data.cond);
    if (condition == NULL) {
        return NULL;
    }

    bool result;
    switch (condition->tag) {
    case TM_DEFAULT:
        result = false;
        break;

    case TM_BOOL_LITERAL:
        result = condition->bool_literal.value;
        break;

    default:
        fatal_error("wrong normal-form for boolean term");
    }
    free_term(condition);

    if (result) {
        return eval_to_normal_form(env, term->if_data.then_branch);
    } else {
        return eval_to_normal_form(env, term->if_data.else_branch);
    }
}


bool compute_unop(struct Location location,
                  struct Type *type,
                  enum UnOp op,
                  uint64_t *x)
{
    switch (op) {
    case UNOP_NEGATE:
        // Note: this is always signed, we do not (currently) allow negation of
        // unsigned values.
        // If the value is 0x800..00 (i.e. just bit 63 set) then it cannot be negated.
        // Otherwise negation will succeed (at least as a 64-bit operation).
        if (*x == UINT64_C(0x8000000000000000)) {
            report_compile_time_overflow(location);
            return false;
        } else {
            *x = -(*x);
            return true;
        }

    case UNOP_COMPLEMENT:
        if (type->tag != TY_FINITE_INT) {
            fatal_error("compute_unop: wrong type");
        }
        *x = ~(*x);
        if (!type->int_data.is_signed) {
            // We do not want to complement the zero-bits to the "left" of the
            // value in this case!
            uint64_t sign_bit = (UINT64_C(1) + 0u) << (type->int_data.num_bits - 1);
            uint64_t keep_bits = (sign_bit - 1u) | sign_bit;
            *x = (*x + 0u) & keep_bits;
        }
        return true;

    case UNOP_NOT:
        *x ^= 1;
        return true;
    }

    fatal_error("bad unop");
}

static struct Term * eval_unop(TypeEnv *env, struct Term *term)
{
    struct Term * operand = eval_to_normal_form(env, term->unop.operand);
    if (!operand) {
        return NULL;
    }

    uint64_t value = normal_form_to_int(operand);
    free_term(operand);

    bool ok = compute_unop(term->location,
                           term->type,
                           term->unop.operator,
                           &value);
    if (ok) {
        if (is_value_in_range_for_type(term->type, value)) {
            return make_literal_of_type(term->type, value);
        } else {
            report_compile_time_overflow(term->location);
            return NULL;
        }
    } else {
        return NULL;
    }
}

bool compute_division(struct Location location,
                      enum BinOp op,
                      bool is_signed,
                      uint64_t *x,
                      uint64_t y)
{
    if (y == 0) {
        report_compile_time_division_by_zero(location);
        return false;
    }

    if (is_signed) {
        int64_t xs, ys;
        memcpy(&xs, x, sizeof(int64_t));
        memcpy(&ys, &y, sizeof(int64_t));

        if (xs == INT64_MIN && ys == -1) {
            report_compile_time_overflow(location);
            return false;
        } else {
            int64_t result;
            if (op == BINOP_DIVIDE) {
                result = xs / ys;
            } else {
                result = xs % ys;
            }
            memcpy(x, &result, 8);
            return true;
        }

    } else {
        if (op == BINOP_DIVIDE) *x = (*x + 0u) / y;
        else *x = (*x + 0u) % y;
        return true;
    }
}

uint64_t compute_comparison(enum BinOp op, bool is_signed, uint64_t x, uint64_t y)
{
    if (is_signed) {
        int64_t xs, ys;
        memcpy(&xs, &x, sizeof(int64_t));
        memcpy(&ys, &y, sizeof(int64_t));

        switch (op) {
        case BINOP_LESS: return xs < ys;
        case BINOP_LESS_EQUAL: return xs <= ys;
        case BINOP_GREATER: return xs > ys;
        case BINOP_GREATER_EQUAL: return xs >= ys;
        default: fatal_error("bad cmp op");
        }

    } else {
        switch (op) {
        case BINOP_LESS: return x < y;
        case BINOP_LESS_EQUAL: return x <= y;
        case BINOP_GREATER: return x > y;
        case BINOP_GREATER_EQUAL: return x >= y;
        default: fatal_error("bad cmp op");
        }
    }
}

bool compute_addition(struct Location location,
                      bool is_signed,
                      uint64_t *x,
                      uint64_t y)
{
    uint64_t result = (*x + 0u) + y;
    if (is_signed) {
        uint64_t sign_bit = UINT64_C(0x8000000000000000);
        bool x_sign = (((*x + 0u) & sign_bit) != 0);
        bool y_sign = (((y + 0u) & sign_bit) != 0);
        bool result_sign = (((result + 0u) & sign_bit) != 0);
        if (x_sign == y_sign && x_sign != result_sign) {
            report_compile_time_overflow(location);
            return false;
        }
    } else {
        if (result < y) {
            report_compile_time_overflow(location);
            return false;
        }
    }
    *x = result;
    return true;
}

// Based on stack overflow answer:
// https://stackoverflow.com/questions/31652875/fastest-way-to-multiply-two-64-bit-ints-to-128-bit-then-to-64-bit
void umul64wide(uint64_t a, uint64_t b, uint64_t *hi, uint64_t *lo)
{
    uint64_t a_lo = (uint64_t)(uint32_t)a;
    uint64_t a_hi = (a + 0u) >> 32;
    uint64_t b_lo = (uint64_t)(uint32_t)b;
    uint64_t b_hi = (b + 0u) >> 32;

    uint64_t p0 = (a_lo + 0u) * b_lo;
    uint64_t p1 = (a_lo + 0u) * b_hi;
    uint64_t p2 = (a_hi + 0u) * b_lo;
    uint64_t p3 = (a_hi + 0u) * b_hi;

    uint32_t cy = (uint32_t)( ( ((p0 + 0u) >> 32)
                                + (uint32_t)p1
                                + (uint32_t)p2)
                              >> 32);

    *lo = (p0 + 0u) + (p1 << 32) + (p2 << 32);
    *hi = (p3 + 0u) + (p1 >> 32) + (p2 >> 32) + cy;
}

void mul64wide(int64_t a, int64_t b, int64_t *hi, int64_t *lo)
{
    umul64wide( (uint64_t)a, (uint64_t)b, (uint64_t*)hi, (uint64_t*)lo );
    if (a < 0) *hi -= b;
    if (b < 0) *hi -= a;
}

// returns true if good, false if overflow
bool multiply_with_overflow_check(bool is_signed,
                                  uint64_t x,
                                  uint64_t y,
                                  uint64_t *result)
{
    uint64_t hi;
    if (is_signed) {
        int64_t a, b;
        memcpy(&a, &x, 8);
        memcpy(&b, &y, 8);
        mul64wide(a, b, (int64_t*)&hi, (int64_t*)result);
        uint64_t sign_bit = (UINT64_C(1) + 0u) << 63;
        if ((*result + 0u) & sign_bit) {
            return hi == UINT64_MAX;
        } else {
            return hi == 0;
        }
    } else {
        umul64wide(x, y, &hi, result);
        return hi == 0;
    }
}

bool compute_binop(struct Location location,
                   enum BinOp op,
                   bool is_signed,
                   uint64_t *x,
                   uint64_t y)
{
    switch (op) {
    case BINOP_PLUS:
        return compute_addition(location, is_signed, x, y);

    case BINOP_MINUS:
        if (is_signed) {
            // negate y, then add
            y = -(y + 0u);
            return compute_addition(location, is_signed, x, y);
        } else {
            // overflow if y > x
            if (y > *x) {
                report_compile_time_overflow(location);
                return false;
            } else {
                *x = *x + 0u - y;
                return true;
            }
        }

    case BINOP_TIMES:
        {
            uint64_t result;
            if (multiply_with_overflow_check(is_signed, *x, y, &result)) {
                *x = result;
                return true;
            } else {
                report_compile_time_overflow(location);
                return false;
            }
        }

    case BINOP_DIVIDE:
    case BINOP_MODULO:
        return compute_division(location, op, is_signed, x, y);

    case BINOP_BITAND:
    case BINOP_AND:
        *x = (*x + 0u) & y;
        return true;

    case BINOP_BITOR:
    case BINOP_OR:
        *x = (*x + 0u) | y;
        return true;

    case BINOP_BITXOR:
        *x = (*x + 0u) ^ y;
        return true;

    case BINOP_SHIFTLEFT:
        if (y >= 64) {
            report_compile_time_invalid_shift_amount(location);
            return false;
        } else {
            *x = (*x + 0u) << y;
            return true;
        }

    case BINOP_SHIFTRIGHT:
        if (y >= 64) {
            report_compile_time_invalid_shift_amount(location);
            return false;
        } else if (y == 0) {
            // no-op
            return true;
        } else if (is_signed && ((*x + 0u) & UINT64_C(0x8000000000000000))) {
            // Simulate a signed right shift (with signed bit set)
            uint64_t ones = UINT64_MAX;
            ones = (ones + 0u) << (64 - y);
            *x = (ones + 0u) | ((*x + 0u) >> y);
            return true;
        }
        // Unsigned right shift
        *x = (*x + 0u) >> y;
        return true;

    case BINOP_EQUAL:
    case BINOP_IFF:
        *x = (*x == y);
        return true;

    case BINOP_NOT_EQUAL:
        *x = (*x != y);
        return true;

    case BINOP_LESS:
    case BINOP_LESS_EQUAL:
    case BINOP_GREATER:
    case BINOP_GREATER_EQUAL:
        *x = compute_comparison(op, is_signed, *x, y);
        return true;

    case BINOP_IMPLIES:
        if (*x == 0) {
            *x = 1;
        } else {
            *x = y;
        }
        return true;

    case BINOP_IMPLIED_BY:
        fatal_error("this term should have been removed by typechecker");
    }

    fatal_error("bad binop");
}

static struct Term * eval_binop(TypeEnv *env, struct Term *term)
{
    if (term->binop.list->next) {
        fatal_error("unexpected operator chaining");
    }

    struct Term *lhs = eval_to_normal_form(env, term->binop.lhs);
    if (!lhs) {
        return NULL;
    }
    uint64_t lhs_value = normal_form_to_int(lhs);
    free_term(lhs);

    // Short circuit operators require special handling, to prevent spurious
    // errors with rhs evaluation
    uint64_t rhs_value = 0;
    enum BinOp op = term->binop.list->operator;
    if ((op == BINOP_IMPLIES || op == BINOP_AND) && lhs_value == 0) {
        rhs_value = 0;
    } else if (op == BINOP_OR && lhs_value == 1) {
        rhs_value = 0;
    } else {
        // rhs must be evaluated
        struct Term *rhs = eval_to_normal_form(env, term->binop.list->rhs);
        if (!rhs) {
            return NULL;
        }
        rhs_value = normal_form_to_int(rhs);
        free_term(rhs);
    }

    bool is_signed = term->binop.lhs->type->tag == TY_FINITE_INT ?
        term->binop.lhs->type->int_data.is_signed :
        false;
    bool ok = compute_binop(term->location,
                            op,
                            is_signed,
                            &lhs_value,
                            rhs_value);
    if (ok) {
        if (is_value_in_range_for_type(term->type, lhs_value)) {
            return make_literal_of_type(term->type, lhs_value);
        } else {
            report_compile_time_overflow(term->location);
            return NULL;
        }
    } else {
        return NULL;
    }
}


static struct Term * eval_let(TypeEnv *env, struct Term *term)
{
    struct Term *rhs = eval_to_normal_form(env, term->let.rhs);
    if (!rhs) return NULL;

    // We will temporarily add the let-bound variable to the env
    // (removing it again afterwards)
    if (type_env_lookup(env, term->let.name) != NULL) {
        fatal_error("let-var already in env (unexpected)");
    }
    struct TypeEnvEntry *entry = alloc(sizeof(struct TypeEnvEntry));
    memset(entry, 0, sizeof(struct TypeEnvEntry));
    // we only need to set entry->value, as that is the only thing we look at
    entry->value = rhs;
    hash_table_insert(env->table, term->let.name, entry);

    // Evaluate the body
    struct Term *body = eval_to_normal_form(env, term->let.body);

    // Remove the bound variable from the env
    hash_table_remove(env->table, term->let.name);
    free_term(rhs);
    free(entry);

    return body;
}

static struct Term * eval_record(TypeEnv *env, struct Term *term)
{
    struct NameTermList *output = NULL;
    struct NameTermList **tail = &output;

    for (struct NameTermList *input = term->record.fields; input; input = input->next) {
        struct Term *normal_form = eval_to_normal_form(env, input->term);

        if (!normal_form) {
            free_name_term_list(output);
            return NULL;
        }

        *tail = alloc(sizeof(struct NameTermList));
        (*tail)->name = copy_string(input->name);
        (*tail)->term = normal_form;
        (*tail)->next = NULL;
        tail = &((*tail)->next);
    }

    struct Term *result = make_term(g_no_location, TM_RECORD);
    result->record.fields = output;
    result->type = copy_type(term->type);
    return result;
}

static struct Term * eval_record_update(TypeEnv *env, struct Term *term)
{
    // Evaluate LHS to normal form - this could be TM_DEFAULT or TM_RECORD
    struct Term *lhs = eval_to_normal_form(env, term->record_update.lhs);
    if (!lhs) return NULL;

    // If it's TM_DEFAULT, change it into TM_RECORD.
    if (lhs->tag == TM_DEFAULT) {
        free_term(lhs);
        lhs = make_term(g_no_location, TM_RECORD);
        lhs->type = copy_type(term->type);
        lhs->record.fields = NULL;

        struct NameTermList **tail = &lhs->record.fields;
        for (struct NameTypeList *field = term->type->record_data.fields; field; field = field->next) {
            *tail = alloc(sizeof(struct NameTermList));
            (*tail)->name = copy_string(field->name);
            (*tail)->term = make_term(g_no_location, TM_DEFAULT);
            (*tail)->term->type = copy_type(field->type);
            (*tail)->next = NULL;
            tail = &((*tail)->next);
        }
    }

    if (lhs->tag != TM_RECORD) fatal_error("bad normal form for record");

    // Now apply each update in turn.
    for (struct NameTermList *update = term->record_update.fields; update; update = update->next) {
        struct Term *normal_form = eval_to_normal_form(env, update->term);
        if (!normal_form) {
            free_term(lhs);
            return NULL;
        }

        struct NameTermList *search;
        for (search = lhs->record.fields; search; search = search->next) {
            if (strcmp(search->name, update->name) == 0) {
                free_term(search->term);
                search->term = normal_form;
                break;
            }
        }
        if (search == NULL) fatal_error("updated field not found");
    }

    // Return the updated lhs.
    return lhs;
}

static struct Term * eval_field_proj(TypeEnv *env, struct Term *term)
{
    struct Term *lhs = eval_to_normal_form(env, term->field_proj.lhs);
    if (!lhs) {
        return NULL;
    }

    if (lhs->tag == TM_DEFAULT) {
        free_term(lhs);
        struct Term *result = make_term(g_no_location, TM_DEFAULT);
        result->type = copy_type(term->type);
        return result;
    }

    if (lhs->tag != TM_RECORD) fatal_error("bad normal form for record");

    for (struct NameTermList *search = lhs->record.fields; search; search = search->next) {
        if (strcmp(search->name, term->field_proj.field_name) == 0) {
            struct Term *result = search->term;
            search->term = NULL;
            free_term(lhs);
            return result;
        }
    }

    fatal_error("projected field not found");
}

static struct Term * eval_variant(TypeEnv *env, struct Term *term)
{
    struct Term *payload = eval_to_normal_form(env, term->variant.payload);
    if (!payload) return NULL;

    struct Term *result = make_term(g_no_location, TM_VARIANT);
    result->type = copy_type(term->type);
    result->variant.variant_name = copy_string(term->variant.variant_name);
    result->variant.payload = payload;
    return result;
}

static struct Term * eval_match(TypeEnv *env, struct Term *term)
{
    // After typechecking, match is only applied to variant types.
    if (term->match.scrutinee->type->tag != TY_VARIANT) {
        fatal_error("match applied to non-variant");
    }

    // Evaluate the scrutinee - will be TM_DEFAULT or TM_VARIANT
    struct Term *scrut = eval_to_normal_form(env, term->match.scrutinee);
    if (!scrut) return NULL;

    // Find out which variant it is.
    const char *variant_name = NULL;
    struct Term *payload = NULL;
    if (scrut->tag == TM_DEFAULT) {
        variant_name = term->type->variant_data.variants->name;
        payload = make_term(g_no_location, TM_DEFAULT);
        payload->type = copy_type(term->type->variant_data.variants->type);
    } else if (scrut->tag == TM_VARIANT) {
        variant_name = scrut->variant.variant_name;
        payload = copy_term(scrut->variant.payload);
    } else {
        fatal_error("bad normal form for variant");
    }

    // Find which arm matches (if any), and the variable name (if any)
    struct Arm *arm;
    const char *variable_name = NULL;
    for (arm = term->match.arms; arm; arm = arm->next) {
        if (arm->pattern->tag == PAT_VARIANT) {
            if (strcmp(arm->pattern->variant.variant_name, variant_name) == 0) {
                if (arm->pattern->variant.payload->tag == PAT_VAR) {
                    variable_name = arm->pattern->variant.payload->var.name;
                }
                break;
            }
        } else if (arm->pattern->tag == PAT_WILDCARD) {
            break;
        } else {
            fatal_error("unexpected pattern");
        }
    }
    if (arm == NULL) {
        // This shouldn't happen because the match compiler will
        // insert TM_MATCH_FAILURE if required.
        fatal_error("no match found");
    }

    // Similarly to TM_LET, add the variable to the env
    struct TypeEnvEntry *entry = NULL;
    if (variable_name) {
        if (type_env_lookup(env, variable_name) != NULL) {
            fatal_error("env already contains variable (unexpected)");
        }
        entry = alloc(sizeof(struct TypeEnvEntry));
        memset(entry, 0, sizeof(struct TypeEnvEntry));
        entry->value = payload;
        hash_table_insert(env->table, variable_name, entry);
    }

    // Now we can evaluate the arm's rhs
    struct Term *result = eval_to_normal_form(env, arm->rhs);

    // Remove the variable if necessary
    if (variable_name) {
        hash_table_remove(env->table, variable_name);
        free(entry);
    }

    free_term(payload);
    free_term(scrut);

    return result;
}

static struct Term * make_sizeof_tuple(const struct TypeData_Array *data)
{
    struct NameTermList *output = NULL;
    struct NameTermList **tail = &output;
    char buf[50];

    struct NameTypeList *types = NULL;
    struct NameTypeList **type_tail = &types;

    for (int i = 0; i < data->ndim; ++i) {
        sprintf(buf, "%d", i);

        *tail = alloc(sizeof(struct NameTermList));
        (*tail)->name = copy_string(buf);
        (*tail)->term = copy_term(data->sizes[i]);
        (*tail)->next = NULL;
        tail = &((*tail)->next);

        *type_tail = alloc(sizeof(struct NameTypeList));
        (*type_tail)->name = copy_string(buf);
        (*type_tail)->type = copy_type(data->sizes[i]->type);
        (*type_tail)->next = NULL;
        type_tail = &((*type_tail)->next);
    }

    struct Term *result = make_term(g_no_location, TM_RECORD);
    result->record.fields = output;
    result->type = make_type(g_no_location, TY_RECORD);
    result->type->record_data.fields = types;
    return result;
}

static struct Term * eval_array_literal(TypeEnv *env, struct Term *term)
{
    struct OpTermList *sub_terms = NULL;
    struct OpTermList **tail = &sub_terms;

    for (struct OpTermList *node = term->array_literal.terms; node; node = node->next) {
        struct Term *sub_term = eval_to_normal_form(env, node->rhs);
        if (sub_term == NULL) {
            free_op_term_list(sub_terms);
            return NULL;
        }
        *tail = alloc(sizeof(struct OpTermList));
        (*tail)->operator = BINOP_PLUS;  // dummy value
        (*tail)->rhs = sub_term;
        (*tail)->next = NULL;
        tail = &(*tail)->next;
    }

    struct Term *result = make_term(g_no_location, TM_ARRAY_LITERAL);
    result->type = copy_type(term->type);
    result->array_literal.terms = sub_terms;
    return result;
}

static struct Term * eval_array_proj(TypeEnv *env, struct Term *term)
{
    struct Term * lhs = eval_to_normal_form(env, term->array_proj.lhs);
    if (lhs == NULL) {
        return NULL;
    }

    if (term->array_proj.indexes == NULL || term->array_proj.indexes->next != NULL) {
        // Array normal-forms can only be one-dimensional (currently), so this
        // would not be type-correct
        fatal_error("eval_array_proj: was expecting only one index");
    }

    if (lhs->tag == TM_CAST) {
        // Casting T[n] to T[]. We can just ignore this.
        struct Term *new_lhs = lhs->cast.operand;
        lhs->cast.operand = NULL;
        free_term(lhs);
        lhs = new_lhs;
    }
    if (lhs->tag != TM_ARRAY_LITERAL) {
        // TM_ARRAY_LITERAL is the only possible normal-form with an array type
        // (once the cast has been stripped away)
        fatal_error("eval_array_proj: unexpected term tag");
    }

    struct Term *index = eval_to_normal_form(env, term->array_proj.indexes->rhs);
    if (index == NULL) {
        free_term(lhs);
        return NULL;
    }

    uint64_t i = normal_form_to_int(index);
    free_term(index);
    index = NULL;

    for (struct OpTermList *node = lhs->array_literal.terms; node; node = node->next) {
        if (i == 0) {
            struct Term *result = copy_term(node->rhs);
            free_term(lhs);
            return result;
        }
        --i;
    }

    report_const_out_of_bounds(term->array_proj.indexes->rhs->location);
    free_term(lhs);
    return NULL;
}

struct Term * eval_to_normal_form(TypeEnv *env, struct Term *term)
{
    switch (term->tag) {
    case TM_VAR:
        return eval_var(env, term);

    case TM_DEFAULT:
    case TM_BOOL_LITERAL:
    case TM_INT_LITERAL:
    case TM_STRING_LITERAL:
        // These are already in normal-form
        return copy_term(term);

    case TM_ARRAY_LITERAL:
        return eval_array_literal(env, term);

    case TM_CAST:
        return eval_cast(env, term);

    case TM_IF:
        return eval_if(env, term);

    case TM_UNOP:
        return eval_unop(env, term);

    case TM_BINOP:
        return eval_binop(env, term);

    case TM_LET:
        return eval_let(env, term);

    case TM_RECORD:
        return eval_record(env, term);

    case TM_RECORD_UPDATE:
        return eval_record_update(env, term);

    case TM_FIELD_PROJ:
        return eval_field_proj(env, term);

    case TM_VARIANT:
        return eval_variant(env, term);

    case TM_MATCH:
        return eval_match(env, term);

    case TM_MATCH_FAILURE:
        report_compile_time_match_failure(term->location);
        return NULL;

    case TM_SIZEOF:
        ;
        struct Type *arr_type = term->sizeof_data.rhs->type;
        if (arr_type->tag == TY_ARRAY && arr_type->array_data.sizes != NULL) {
            // fixed array sizes are already in normal-form, just need to
            // copy (and make into a tuple if necessary)
            if (arr_type->array_data.ndim == 1) {
                return copy_term(arr_type->array_data.sizes[0]);
            } else {
                return make_sizeof_tuple(&arr_type->array_data);
            }
        } else {
            return NULL;
        }

    case TM_ARRAY_PROJ:
        return eval_array_proj(env, term);

    case TM_QUANTIFIER:
    case TM_CALL:
    case TM_TYAPP:
    case TM_ALLOCATED:
        report_non_compile_time_constant(term->location);
        return NULL;
    }

    fatal_error("unrecognised term tag");
}
