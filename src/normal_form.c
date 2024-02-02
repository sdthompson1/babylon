/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "ast.h"
#include "error.h"
#include "normal_form.h"

#include <inttypes.h>
#include <stdio.h>
#include <string.h>

uint64_t parse_int_literal(const char *data)
{
    bool negative = false;
    if (data[0] == '-') {
        negative = true;
        ++data;
    }

    uint64_t result = 0;

    for (; *data; ++data) {
        result = result * 10 + (*data - '0');
    }

    if (negative) {
        result = -result;
    }

    return result;
}

uint64_t normal_form_to_int(const struct Term *term)
{
    switch (term->tag) {
    case TM_DEFAULT:
        return 0;

    case TM_INT_LITERAL:
        return parse_int_literal(term->int_literal.data);

    case TM_BOOL_LITERAL:
        return term->bool_literal.value ? 1 : 0;

    default:
        fatal_error("cannot convert normal form to integer");
    }
}

static struct Term * make_signed_int_literal(int64_t value)
{
    char buf[50];
    sprintf(buf, "%" PRIi64, value);
    return make_int_literal_term(g_no_location, buf);
}

static struct Term * make_unsigned_int_literal(uint64_t value)
{
    char buf[50];
    sprintf(buf, "%" PRIu64, value);
    return make_int_literal_term(g_no_location, buf);
}

static uint64_t normalise_to_type(struct Type *type, uint64_t value)
{
    if (type->tag != TY_FINITE_INT) fatal_error("normalise_to_type called with wrong type");
    if (type->int_data.num_bits == 64) return value;  // nothing needed

    uint64_t ones = (uint64_t)-1;
    ones <<= type->int_data.num_bits;

    value = value & ~ones;  // mask to the bottom bits only

    if (type->int_data.is_signed && (value & (ones >> 1))) {
        // sign bit is set
        value |= ones;
    }

    return value;
}

struct Term * make_literal_of_type(struct Type *type, uint64_t value)
{
    struct Term *result = NULL;

    switch (type->tag) {
    case TY_FINITE_INT:
        value = normalise_to_type(type, value);
        if (type->int_data.is_signed) {
            int64_t signed_value;
            memcpy(&signed_value, &value, sizeof(int64_t));
            result = make_signed_int_literal(signed_value);
        } else {
            result = make_unsigned_int_literal(value);
        }
        break;

    case TY_BOOL:
        result = make_bool_literal_term(g_no_location, value != 0);
        break;

    default:
        fatal_error("cannot make a literal of this type");
    }

    result->type = copy_type(type);
    return result;
}
