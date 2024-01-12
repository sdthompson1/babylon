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
#include "hash_table.h"
#include "normal_form.h"
#include "typechecker.h"   // for TypeEnvEntry
#include "util.h"

#include <stdlib.h>
#include <string.h>

static struct Term * eval_var(struct HashTable *env, struct Term *term)
{
    struct TypeEnvEntry *entry = hash_table_lookup(env, term->var.name);
    if (entry && entry->value) {
        return copy_term(entry->value);
    } else {
        return NULL;
    }
}

static struct Term * eval_cast(struct HashTable *env, struct Term *term)
{
    // a cast doesn't change the value, but it does change the type.
    struct Term *result = eval_to_normal_form(env, term->cast.operand);
    free_type(result->type);
    result->type = copy_type(term->type);
    return result;
}

static struct Term * eval_if(struct HashTable *env, struct Term *term)
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


uint64_t compute_unop(enum UnOp op, uint64_t x)
{
    switch (op) {
    case UNOP_NEGATE:
        return -x;

    case UNOP_COMPLEMENT:
        return ~x;

    case UNOP_NOT:
        return x ^ 1;
    }

    fatal_error("bad unop");
}

static struct Term * eval_unop(struct HashTable *env, struct Term *term)
{
    struct Term * operand = eval_to_normal_form(env, term->unop.operand);
    if (!operand) {
        return NULL;
    }

    uint64_t value = normal_form_to_int(operand);
    free_term(operand);

    value = compute_unop(term->unop.operator, value);
    return make_literal_of_type(term->type, value);
}


uint64_t compute_division(enum BinOp op, bool is_signed, uint64_t x, uint64_t y)
{
    // This will just return 0 if the division is undefined or would overflow.

    if (y == 0) {
        return 0;
    }

    if (is_signed) {
        int64_t xs, ys;
        memcpy(&xs, &x, sizeof(int64_t));
        memcpy(&ys, &y, sizeof(int64_t));

        if (xs == INT64_MIN && ys == -1) {
            // would overflow
            return 0;
        } else {
            if (op == BINOP_DIVIDE) return xs / ys;
            else return xs % ys;
        }

    } else {
        if (op == BINOP_DIVIDE) return x / y;
        else return x % y;
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

uint64_t compute_binop(enum BinOp op, bool is_signed, uint64_t x, uint64_t y)
{
    switch (op) {
    case BINOP_PLUS:
        return x + y;

    case BINOP_MINUS:
        return x - y;

    case BINOP_TIMES:
        return x * y;

    case BINOP_DIVIDE:
    case BINOP_MODULO:
        return compute_division(op, is_signed, x, y);

    case BINOP_BITAND:
    case BINOP_AND:
        return x & y;

    case BINOP_BITOR:
    case BINOP_OR:
        return x | y;

    case BINOP_BITXOR:
        return x ^ y;

    case BINOP_SHIFTLEFT:
        return x << y;

    case BINOP_SHIFTRIGHT:
        if (is_signed) {
            // Strictly speaking, C11 doesn't guarantee that signed >> does what you would expect.
            // Therefore compute the shift "manually".
            if (y == 0) {
                return x;
            } else {
                uint64_t ones = (uint64_t)-1;
                ones <<= (64 - x);
                return ones | (x >> y);
            }
        } else {
            return x >> y;
        }
        break;

    case BINOP_EQUAL:
    case BINOP_IFF:
        return x == y;

    case BINOP_NOT_EQUAL:
        return x != y;

    case BINOP_LESS:
    case BINOP_LESS_EQUAL:
    case BINOP_GREATER:
    case BINOP_GREATER_EQUAL:
        return compute_comparison(op, is_signed, x, y);

    case BINOP_IMPLIES:
        if (x == 0) {
            return 1;
        } else {
            return y;
        }

    case BINOP_IMPLIED_BY:
        fatal_error("this term should have been removed by typechecker");
    }

    fatal_error("bad binop");
}

static struct Term * eval_binop(struct HashTable *env, struct Term *term)
{
    if (term->binop.list->next) {
        fatal_error("unexpected operator chaining");
    }

    struct Term *lhs = eval_to_normal_form(env, term->binop.lhs);
    struct Term *rhs = eval_to_normal_form(env, term->binop.list->rhs);
    if (!lhs || !rhs) {
        free_term(lhs);
        free_term(rhs);
        return NULL;
    }

    bool is_signed = lhs->type->tag == TY_FINITE_INT ? lhs->type->int_data.is_signed : false;
    uint64_t lhs_value = normal_form_to_int(lhs);
    uint64_t rhs_value = normal_form_to_int(rhs);
    free_term(lhs);
    free_term(rhs);

    uint64_t result = compute_binop(term->binop.list->operator, is_signed, lhs_value, rhs_value);
    return make_literal_of_type(term->type, result);
}


static struct Term * eval_let(struct HashTable *env, struct Term *term)
{
    struct Term *rhs = eval_to_normal_form(env, term->let.rhs);
    if (!rhs) return NULL;

    // We will temporarily add the let-bound variable to the env
    // (removing it again afterwards)
    if (hash_table_contains_key(env, term->let.name)) {
        fatal_error("let-var already in env (unexpected)");
    }
    struct TypeEnvEntry *entry = alloc(sizeof(struct TypeEnvEntry));
    // we only need to set entry->value, as that is the only thing we look at
    entry->value = rhs;
    hash_table_insert(env, term->let.name, entry);

    // Evaluate the body
    struct Term *body = eval_to_normal_form(env, term->let.body);

    // Remove the bound variable from the env
    hash_table_remove(env, term->let.name);
    free_term(rhs);
    free(entry);

    return body;
}

static struct Term * eval_record(struct HashTable *env, struct Term *term)
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

static struct Term * eval_record_update(struct HashTable *env, struct Term *term)
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

static struct Term * eval_field_proj(struct HashTable *env, struct Term *term)
{
    struct Term *lhs = eval_to_normal_form(env, term->field_proj.lhs);

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

static struct Term * eval_variant(struct HashTable *env, struct Term *term)
{
    struct Term *payload = eval_to_normal_form(env, term->variant.payload);
    if (!payload) return NULL;

    struct Term *result = make_term(g_no_location, TM_VARIANT);
    result->type = copy_type(term->type);
    result->variant.variant_name = copy_string(term->variant.variant_name);
    result->variant.payload = payload;
    return result;
}

static struct Term * eval_match(struct HashTable *env, struct Term *term)
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
        if (hash_table_contains_key(env, variable_name)) {
            fatal_error("env already contains variable (unexpected)");
        }
        entry = alloc(sizeof(struct TypeEnvEntry));
        entry->value = payload;
        hash_table_insert(env, variable_name, entry);
    }

    // Now we can evaluate the arm's rhs
    struct Term *result = eval_to_normal_form(env, arm->rhs);

    // Remove the variable if necessary
    if (variable_name) {
        hash_table_remove(env, variable_name);
        free(entry);
    }

    free_term(payload);
    free_term(scrut);

    return result;
}

struct Term * eval_to_normal_form(struct HashTable *env, struct Term *term)
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

    case TM_QUANTIFIER:
    case TM_CALL:
    case TM_TYAPP:
        return NULL;

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
        {
            struct Term *dflt = make_term(g_no_location, TM_DEFAULT);
            dflt->type = copy_type(term->type);
            return dflt;
        }

    case TM_SIZEOF:
    case TM_ALLOCATED:
    case TM_ARRAY_PROJ:
        return NULL;
    }

    fatal_error("unrecognised term tag");
}
