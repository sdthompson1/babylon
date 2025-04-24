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

uint64_t normal_form_to_int(const struct Term *term)
{
    switch (term->tag) {
    case TM_DEFAULT:
        return 0;

    case TM_INT_LITERAL:
        return term->int_literal.value;

    case TM_BOOL_LITERAL:
        return term->bool_literal.value ? 1 : 0;

    default:
        fatal_error("cannot convert normal form to integer");
    }
}

bool is_value_in_range_for_type(struct Type *type, uint64_t value)
{
    if (type->tag == TY_BOOL) {
        return value == 0 || value == 1;
    }

    if (type->tag != TY_FINITE_INT) {
        fatal_error("is_value_in_range_for_type called with wrong type");
    }

    int bits = type->int_data.num_bits;
    bool s = type->int_data.is_signed;

    switch (bits) {
    case 8:
        if (s) return value <= UINT64_C(0x7f)
                   || value >= UINT64_C(0xffffffffffffff80);
        else return value <= UINT64_C(0xff);

    case 16:
        if (s) return value <= UINT64_C(0x7fff)
                   || value >= UINT64_C(0xffffffffffff8000);
        else return value <= UINT64_C(0xffff);

    case 32:
        if (s) return value <= UINT64_C(0x7fffffff)
                   || value >= UINT64_C(0xffffffff80000000);
        else return value <= UINT64_C(0xffffffff);

    case 64:
        return true;

    default:
        fatal_error("is_value_in_range_for_type: invalid num_bits");
    }
}

struct Term * make_literal_of_type(struct Type *type, uint64_t value)
{
    struct Term *result = NULL;

    switch (type->tag) {
    case TY_FINITE_INT:
        if (!is_value_in_range_for_type(type, value)) {
            fatal_error("make_literal_of_type (TY_FINITE_INT): value is out of range");
        }
        if (type->int_data.is_signed) {
            int64_t signed_value;
            memcpy(&signed_value, &value, sizeof(int64_t));
            result = make_signed_int_literal_term(g_no_location, signed_value);
        } else {
            result = make_unsigned_int_literal_term(g_no_location, value);
        }
        break;

    case TY_BOOL:
        if (value != 0 && value != 1) {
            fatal_error("make_literal_of_type (TY_BOOL): value is not 0 or 1");
        }
        result = make_bool_literal_term(g_no_location, value != 0);
        break;

    default:
        fatal_error("cannot make a literal of this type");
    }

    result->type = copy_type(type);
    return result;
}
