/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"
#include "sexpr.h"
#include "stringbuf.h"
#include "util.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct Sexpr * make_string_sexpr(const char *data)
{
    return make_string_sexpr_handover(copy_string(data));
}

struct Sexpr * make_string_sexpr_handover(const char *data)
{
    struct Sexpr * expr = alloc(sizeof(struct Sexpr));
    expr->type = S_STRING;
    expr->string = data;
    return expr;
}

struct Sexpr * make_pair_sexpr(struct Sexpr *left, struct Sexpr *right)
{
    struct Sexpr * expr = alloc(sizeof(struct Sexpr));
    expr->type = S_PAIR;
    expr->left = left;
    expr->right = right;
    return expr;
}

void* transform_sexpr(struct SexprTransform *tr, void *context, struct Sexpr *sexpr)
{
    if (sexpr == NULL) {
        return NULL;
    }

    switch (sexpr->type) {
    case S_STRING:
        if (tr->transform_string) {
            return tr->transform_string(context, sexpr);
        } else {
            return NULL;
        }

    case S_PAIR:
        {
            void *left = transform_sexpr(tr, context, sexpr->left);
            void *right = transform_sexpr(tr, context, sexpr->right);
            if (tr->transform_pair) {
                return tr->transform_pair(context, sexpr, left, right);
            } else {
                return NULL;
            }
        }
    }

    fatal_error("unexpected sexpr type");
}

static void* copy_string_sexpr(void *context, struct Sexpr *sexpr)
{
    return make_string_sexpr(sexpr->string);
}

static void* copy_pair_sexpr(void *context, struct Sexpr *sexpr, void *left, void *right)
{
    return make_pair_sexpr(left, right);
}

struct Sexpr * copy_sexpr(struct Sexpr *input)
{
    struct SexprTransform tr = {0};
    tr.transform_string = copy_string_sexpr;
    tr.transform_pair = copy_pair_sexpr;
    return transform_sexpr(&tr, NULL, input);
}

static void* free_string_sexpr(void *context, struct Sexpr *sexpr)
{
    free((char*)sexpr->string);
    free(sexpr);
    return NULL;
}

static void* free_pair_sexpr(void *context, struct Sexpr *sexpr, void *left, void *right)
{
    free(sexpr);
    return NULL;
}

void free_sexpr(struct Sexpr *sexpr)
{
    struct SexprTransform tr = {0};
    tr.transform_string = free_string_sexpr;
    tr.transform_pair = free_pair_sexpr;
    transform_sexpr(&tr, NULL, sexpr);
}

struct Sexpr * make_list1_sexpr(struct Sexpr *s1)
{
    return make_pair_sexpr(s1, NULL);
}

struct Sexpr * make_list2_sexpr(struct Sexpr *s1, struct Sexpr *s2)
{
    return make_pair_sexpr(s1, make_list1_sexpr(s2));
}

struct Sexpr * make_list3_sexpr(struct Sexpr *s1, struct Sexpr *s2, struct Sexpr *s3)
{
    return make_pair_sexpr(s1, make_list2_sexpr(s2, s3));
}

struct Sexpr * make_list4_sexpr(struct Sexpr *s1, struct Sexpr *s2, struct Sexpr *s3, struct Sexpr *s4)
{
    return make_pair_sexpr(s1, make_list3_sexpr(s2, s3, s4));
}

struct Sexpr * make_list5_sexpr(struct Sexpr *s1, struct Sexpr *s2, struct Sexpr *s3, struct Sexpr *s4, struct Sexpr *s5)
{
    return make_pair_sexpr(s1, make_list4_sexpr(s2, s3, s4, s5));
}

int get_sexpr_list_length(const struct Sexpr *s)
{
    int length = 0;

    while (s) {
        if (s->type != S_PAIR) {
            return -1;
        }
        ++length;
        s = s->right;
    }

    return length;
}

void format_sexpr(struct StringBuf *buf, const struct Sexpr *expr)
{
    if (expr == NULL) {
        stringbuf_append(buf, "()");
    } else {
        switch (expr->type) {
        case S_STRING:
            stringbuf_append(buf, expr->string);
            break;

        case S_PAIR:
            stringbuf_append(buf, "(");

            while (true) {
                format_sexpr(buf, expr->left);

                expr = expr->right;

                if (expr == NULL) {
                    stringbuf_append(buf, ")");
                    break;

                } else if (expr->type == S_PAIR) {
                    stringbuf_append(buf, " ");

                } else {
                    stringbuf_append(buf, " . ");
                    format_sexpr(buf, expr);
                    stringbuf_append(buf, ")");
                    break;
                }
            }
            break;

        default:
            stringbuf_append(buf, "#UNKNOWN");
            break;
        }
    }
}

void print_sexpr(const struct Sexpr *expr)
{
    struct StringBuf buf;
    stringbuf_init(&buf);
    format_sexpr(&buf, expr);
    fprintf(stderr, "%s\n", buf.data);
    stringbuf_free(&buf);
}

bool sexpr_equal(const struct Sexpr *lhs, const struct Sexpr *rhs)
{
    if (lhs == NULL) {
        return (rhs == NULL);
    } else if (rhs == NULL) {
        return false;
    } else if (lhs->type != rhs->type) {
        return false;
    } else if (lhs->type == S_STRING) {
        return strcmp(lhs->string, rhs->string) == 0;
    } else {
        return sexpr_equal(lhs->left, rhs->left)
            && sexpr_equal(lhs->right, rhs->right);
    }
}

bool sexpr_equal_string(const struct Sexpr *lhs, const char *rhs)
{
    return lhs != NULL
        && lhs->type == S_STRING
        && strcmp(lhs->string, rhs) == 0;
}


struct Sexpr *substitute_in_sexpr(const struct Sexpr *keys,
                                  const struct Sexpr *values,
                                  const struct Sexpr *expr)
{
    if (expr == NULL) {
        return NULL;

    } else if (expr->type == S_STRING) {
        // see if this is a name to be substituted
        while (keys) {
            if (sexpr_equal(expr, keys->left)) {
                return copy_sexpr(values->left);
            }
            keys = keys->right;
            values = values->right;
        }

        // no substitution applies to this name, so just copy it to the output
        return copy_sexpr((struct Sexpr*)expr);

    } else if (expr->type == S_PAIR) {

        if (expr->left->type == S_STRING) {
            // expr is a list like (NAME arg1 arg2)
            // let's see if NAME corresponds to a lambda
            const struct Sexpr *keys2 = keys;
            const struct Sexpr *values2 = values;
            while (keys2) {
                if (sexpr_equal(expr->left, keys2->left)) {
                    // we want values2->left to be a list like ($lambda (var1 var2) body)
                    if (values2->left->type == S_PAIR
                    && sexpr_equal_string(values2->left->left, "$lambda")) {

                        // it's a match.
                        return substitute_in_sexpr(values2->left->right->left,
                                                   expr->right,
                                                   values2->left->right->right->left);
                    }

                    // we found the key but the value wasn't a lambda, so give up
                    break;
                }

                keys2 = keys2->right;
                values2 = values2->right;
            }
        }

        // just substitute each child node individually
        struct Sexpr *result = NULL;
        struct Sexpr **next_ptr = &result;
        while (expr) {
            *next_ptr = make_list1_sexpr(substitute_in_sexpr(keys, values, expr->left));
            next_ptr = &(*next_ptr)->right;
            expr = expr->right;
        }
        return result;

    } else {
        fatal_error("unknown sexpr type");
    }
}


bool sexpr_contains_string(const struct Sexpr *sexpr, const char *find)
{
    if (sexpr_equal_string(sexpr, find)) {
        return true;
    } else if (sexpr && sexpr->type == S_PAIR) {
        return sexpr_contains_string(sexpr->left, find) || sexpr_contains_string(sexpr->right, find);
    } else {
        return false;
    }
}
