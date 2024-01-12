/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "ast.h"
#include "error.h"
#include "sexpr.h"
#include "util.h"
#include "verifier_context.h"
#include "verifier_types.h"

#include <stdio.h>

struct Sexpr * verify_type(struct Type *type)
{
    switch (type->tag) {
    case TY_VAR:
        return make_string_sexpr_handover(copy_string_2("%", type->var_data.name));

    case TY_BOOL:
        return make_string_sexpr("Bool");

    case TY_FINITE_INT:
    case TY_MATH_INT:
        return make_string_sexpr("Int");

    case TY_MATH_REAL:
        return make_string_sexpr("Real");

    case TY_RECORD:
        {
            struct Sexpr * types = verify_name_type_list(type->record_data.fields);
            struct Sexpr * result = make_string_sexpr("$PROD");
            make_instance(&result, types);
            return result;
        }

    case TY_VARIANT:
        {
            struct Sexpr * types = verify_name_type_list(type->variant_data.variants);
            struct Sexpr * result = make_string_sexpr("$SUM");
            make_instance(&result, types);
            return result;
        }

    case TY_ARRAY:
        {
            struct Sexpr *element_type = verify_type(type->array_data.element_type);
            struct Sexpr *index_type = array_index_type(type->array_data.ndim);
            struct Sexpr * array_type =
                make_list3_sexpr(make_string_sexpr("Array"),
                                 copy_sexpr(index_type),
                                 element_type);
            struct Sexpr * result = make_string_sexpr("$PROD");
            make_instance(&result, make_list2_sexpr(array_type, index_type));
            return result;
        }

    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
    case TY_APP:
        fatal_error("verify_type: TY_FUNCTION, TY_FORALL, TY_LAMBDA, TY_APP not supported");
    }

    fatal_error("verify_type unknown type");
}

struct Sexpr * verify_name_type_list(struct NameTypeList *types)
{
    struct Sexpr *list = NULL;
    struct Sexpr **tail = &list;
    while (types) {
        struct Sexpr *ty = verify_type(types->type);
        *tail = make_list1_sexpr(ty);
        tail = &((*tail)->right);
        types = types->next;
    }
    return list;
}
