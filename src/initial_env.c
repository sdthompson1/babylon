/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "codegen.h"
#include "hash_table.h"
#include "initial_env.h"
#include "sexpr.h"
#include "typechecker.h"
#include "util.h"
#include "verifier_context.h"

#include <inttypes.h>
#include <stdio.h>
#include <string.h>

// (x Int)
static struct Sexpr *xInt()
{
    return make_list2_sexpr(make_string_sexpr("x"), make_string_sexpr("Int"));
}

// (y Int)
static struct Sexpr *yInt()
{
    return make_list2_sexpr(make_string_sexpr("y"), make_string_sexpr("Int"));
}

// ((x Int) (y Int))
static struct Sexpr *xyInt()
{
    return make_list2_sexpr(xInt(), yInt());
}

// (op x y)
static struct Sexpr *opxy(const char *op)
{
    return make_list3_sexpr(make_string_sexpr(op),
                            make_string_sexpr("x"),
                            make_string_sexpr("y"));
}

// (<= (- absmin) (op x y))
static struct Sexpr *binop_min_check(const char *op, const char *absmin)
{
    struct Sexpr *min_expr = make_list2_sexpr(make_string_sexpr("-"),
                                              make_string_sexpr(absmin));
    struct Sexpr *op_expr = opxy(op);
    return make_list3_sexpr(make_string_sexpr("<="), min_expr, op_expr);
}

// (<= (op x y) max)
static struct Sexpr *binop_max_check(const char *op, const char *max)
{
    struct Sexpr *op_expr = opxy(op);
    struct Sexpr *max_expr = make_string_sexpr(max);
    return make_list3_sexpr(make_string_sexpr("<="), op_expr, max_expr);
}

// (and (<= (- absmin) (op x y))
//      (<= (op x y) max))
static struct Sexpr *binop_minmax_check(const char *op, const char *absmin, const char *max)
{
    return make_list3_sexpr(make_string_sexpr("and"),
                            binop_min_check(op, absmin),
                            binop_max_check(op, max));
}

// (and (<= minexpr x) (<= x max))
static struct Sexpr *x_minmax_check(struct Sexpr *minexpr, const char *max)
{
    return make_list3_sexpr(make_string_sexpr("and"),

                            make_list3_sexpr( make_string_sexpr("<="),
                                              minexpr,
                                              make_string_sexpr("x") ),

                            make_list3_sexpr( make_string_sexpr("<="),
                                              make_string_sexpr("x"),
                                              make_string_sexpr(max) ));
}


// hands over fol_decl, fol_asserts
static void add_fol_helper(struct HashTable *env,
                           const char *name,
                           struct Sexpr *fol_decl,
                           struct Sexpr *fol_axioms)
{
    struct Item *item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));
    item->fol_decl = fol_decl;
    item->fol_axioms = fol_axioms;
    item->fol_name = copy_string(name);
    item->fol_type = NULL;
    item->fol_generic_vars = NULL;
    item->fol_dummies = NULL;
    item->preconds = item->postconds = NULL;
    hash_table_insert(env, copy_string(name), item);
}


static void can_add_u(struct HashTable *env, const char *type, const char *max)
{
    // (define-fun $can_add_u8 ((x Int) (y Int)) Bool
    //  (<= (+ x y) 255))

    char name[20];
    sprintf(name, "$can_add_%s", type);

    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Bool"),
                                          binop_max_check("+", max));

    add_fol_helper(env, name, decl, NULL);
}

static void can_sub_u(struct HashTable *env, const char *type)
{
    // (define-fun $can_sub_u8 ((x Int) (y Int)) Bool
    //  (<= y x))

    char name[20];
    sprintf(name, "$can_sub_%s", type);

    struct Sexpr *body = make_list3_sexpr(make_string_sexpr("<="),
                                          make_string_sexpr("y"),
                                          make_string_sexpr("x"));

    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Bool"),
                                          body);

    add_fol_helper(env, name, decl, NULL);
}

static void can_mul_u(struct HashTable *env, const char *type, const char *max)
{
    // (define-fun $can_mul_u8 ((x Int) (y Int)) Bool
    //  (<= (* x y) 255))

    char name[20];
    sprintf(name, "$can_mul_%s", type);

    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Bool"),
                                          binop_max_check("*", max));

    add_fol_helper(env, name, decl, NULL);
}

static void can_div_u(struct HashTable *env, const char *type)
{
    // (define-fun $can_div_u8 ((x Int) (y Int)) Bool
    //  (distinct y 0))

    char name[20];
    sprintf(name, "$can_div_%s", type);

    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Bool"),
                                          make_list3_sexpr(make_string_sexpr("distinct"),
                                                           make_string_sexpr("y"),
                                                           make_string_sexpr("0")));

    add_fol_helper(env, name, decl, NULL);
}


static void in_range_u(struct HashTable *env, const char *type, const char *max)
{
    // (define-fun $in_range_u8 ((x Int)) Bool
    //  (and (<= 0 x) (<= x 255)))

    char name[20];
    sprintf(name, "$in_range_%s", type);

    struct Sexpr *decl = make_list5_sexpr(
        make_string_sexpr("define-fun"),
        make_string_sexpr(name),
        make_list1_sexpr( xInt() ),
        make_string_sexpr("Bool"),
        x_minmax_check(make_string_sexpr("0"), max));

    add_fol_helper(env, name, decl, NULL);
}

static void can_add_i(struct HashTable *env,
                      const char *type, const char *absmin, const char *max)
{
    // (define-fun $can_add_i8 ((x Int) (y Int)) Bool
    //  (and (<= (- 128) (+ x y))
    //       (<= (+ x y) 127)))

    char name[20];
    sprintf(name, "$can_add_%s", type);

    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Bool"),
                                          binop_minmax_check("+", absmin, max));

    add_fol_helper(env, name, decl, NULL);
}

// copies all char* inputs
static void can_sub_i(struct HashTable *env,
                      const char *type, const char *absmin, const char *max)
{
    // (define-fun $can_sub_i8 ((x Int) (y Int)) Bool
    //  (and (<= (- 128) (- x y))
    //       (<= (- x y) 127)))

    char name[20];
    sprintf(name, "$can_sub_%s", type);

    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Bool"),
                                          binop_minmax_check("-", absmin, max));

    add_fol_helper(env, name, decl, NULL);
}

static void can_mul_i(struct HashTable *env,
                      const char *type, const char *absmin, const char *max)
{
    // (define-fun $can_mul_i8 ((x Int) (y Int)) Bool
    //  (and (<= (- 128) (* x y))
    //       (<= (* x y) 127)))

    char name[20];
    sprintf(name, "$can_mul_%s", type);

    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Bool"),
                                          binop_minmax_check("*", absmin, max));

    add_fol_helper(env, name, decl, NULL);
}

static void can_div_i(struct HashTable *env, const char *type, const char *absmin)
{
    // (define-fun $can_div_i8 ((x Int) (y Int)) Bool
    //  (and (distinct y 0)
    //       (not (and (= x (- absmin)) (= y (- 1))))))

    char name[20];
    sprintf(name, "$can_div_%s", type);

    struct Sexpr *decl =
        make_list5_sexpr(
            make_string_sexpr("define-fun"),
            make_string_sexpr(name),
            xyInt(),
            make_string_sexpr("Bool"),
            make_list3_sexpr(
                make_string_sexpr("and"),
                make_list3_sexpr(
                    make_string_sexpr("distinct"),
                    make_string_sexpr("y"),
                    make_string_sexpr("0")
                ),
                make_list2_sexpr(
                    make_string_sexpr("not"),
                    make_list3_sexpr(
                        make_string_sexpr("and"),
                        make_list3_sexpr(
                            make_string_sexpr("="),
                            make_string_sexpr("x"),
                            make_list2_sexpr(make_string_sexpr("-"), make_string_sexpr(absmin))
                        ),
                        make_list3_sexpr(
                            make_string_sexpr("="),
                            make_string_sexpr("y"),
                            make_list2_sexpr(make_string_sexpr("-"), make_string_sexpr("1"))  )))));

    add_fol_helper(env, name, decl, NULL);
}

static void div_i(struct HashTable *env, const char *type)
{
    // (define-fun $div_i8 ((x Int) (y Int)) Int
    //  (ite (< x 0)
    //       (- (div (- x) y))
    //       (div x y))
    char name[20];
    sprintf(name, "$div_%s", type);

    struct Sexpr *decl =
        make_list5_sexpr(
            make_string_sexpr("define-fun"),
            make_string_sexpr(name),
            xyInt(),
            make_string_sexpr("Int"),
            make_list4_sexpr(
                make_string_sexpr("ite"),
                make_list3_sexpr(
                    make_string_sexpr("<"),
                    make_string_sexpr("x"),
                    make_string_sexpr("0")
                ),
                make_list2_sexpr(
                    make_string_sexpr("-"),
                    make_list3_sexpr(
                        make_string_sexpr("div"),
                        make_list2_sexpr(
                            make_string_sexpr("-"),
                            make_string_sexpr("x")
                        ),
                        make_string_sexpr("y")
                    )
                ),
                make_list3_sexpr(
                    make_string_sexpr("div"),
                    make_string_sexpr("x"),
                    make_string_sexpr("y")
                )));
    add_fol_helper(env, name, decl, NULL);
}

static void mod_i(struct HashTable *env, const char *type)
{
    // (define-fun $mod_i8 ((x Int) (y Int)) Int
    //  (ite (< x 0)
    //       (- (mod (- x) y))
    //       (mod x y))
    char name[20];
    sprintf(name, "$mod_%s", type);

    struct Sexpr *decl =
        make_list5_sexpr(
            make_string_sexpr("define-fun"),
            make_string_sexpr(name),
            xyInt(),
            make_string_sexpr("Int"),
            make_list4_sexpr(
                make_string_sexpr("ite"),
                make_list3_sexpr(
                    make_string_sexpr("<"),
                    make_string_sexpr("x"),
                    make_string_sexpr("0")
                ),
                make_list2_sexpr(
                    make_string_sexpr("-"),
                    make_list3_sexpr(
                        make_string_sexpr("mod"),
                        make_list2_sexpr(
                            make_string_sexpr("-"),
                            make_string_sexpr("x")
                        ),
                        make_string_sexpr("y")
                    )
                ),
                make_list3_sexpr(
                    make_string_sexpr("mod"),
                    make_string_sexpr("x"),
                    make_string_sexpr("y")
                )));
    add_fol_helper(env, name, decl, NULL);
}

static void bitwise(struct HashTable *env, const char *op, bool is_signed, int num_bits)
{
    // (define-fun $and_i8 ((x Int) (y Int)) Int
    //  (+ (ite (and (= (mod x         2) 1) (= (mod y         2) 1)) 1 0)
    //     (ite (and (= (mod (div x 2) 2) 1) (= (mod (div y 2) 2) 1)) 2 0)
    //     (ite (and (= (mod (div x 4) 2) 1) (= (mod (div y 4) 2) 1)) 4 0)
    //     ... )

    uint64_t power = 1;

    struct Sexpr *expr = make_list1_sexpr(make_string_sexpr("+"));
    struct Sexpr **tail = &expr->right;

    for (int i = 0; i < num_bits; ++i) {
        char power_str[30];
        sprintf(power_str, "%" PRIu64, power);

        if (i < num_bits - 1 || !is_signed) {
            struct Sexpr *divx = make_string_sexpr("x");
            struct Sexpr *divy = make_string_sexpr("y");
            if (power != 1) {
                divx = make_list3_sexpr(make_string_sexpr("div"), divx, make_string_sexpr(power_str));
                divy = make_list3_sexpr(make_string_sexpr("div"), divy, make_string_sexpr(power_str));
            }

            *tail =
                make_list1_sexpr(
                    make_list4_sexpr(
                        make_string_sexpr("ite"),
                        make_list3_sexpr(
                            make_string_sexpr(op),  // "and" or "or" or "xor"
                            make_list3_sexpr(
                                make_string_sexpr("="),
                                make_list3_sexpr(
                                    make_string_sexpr("mod"),
                                    divx,
                                    make_string_sexpr("2")),
                                make_string_sexpr("1")),
                            make_list3_sexpr(
                                make_string_sexpr("="),
                                make_list3_sexpr(
                                    make_string_sexpr("mod"),
                                    divy,
                                    make_string_sexpr("2")),
                                make_string_sexpr("1"))),
                        make_string_sexpr(power_str),
                        make_string_sexpr("0")));
        } else {
            *tail =
                make_list1_sexpr(
                    make_list4_sexpr(
                        make_string_sexpr("ite"),
                        make_list3_sexpr(
                            make_string_sexpr(op),
                            make_list3_sexpr(
                                make_string_sexpr("<"),
                                make_string_sexpr("x"),
                                make_string_sexpr("0")),
                            make_list3_sexpr(
                                make_string_sexpr("<"),
                                make_string_sexpr("y"),
                                make_string_sexpr("0"))),
                        make_list2_sexpr(make_string_sexpr("-"), make_string_sexpr(power_str)),
                        make_string_sexpr("0")));
        }
        tail = &(*tail)->right;

        power <<= 1;
    }

    char name[20];
    sprintf(name, "$%s_%s%d", op, is_signed ? "i" : "u", num_bits);

    struct Sexpr *decl = make_list5_sexpr(
        make_string_sexpr("define-fun"),
        make_string_sexpr(name),
        xyInt(),
        make_string_sexpr("Int"),
        expr);

    add_fol_helper(env, name, decl, NULL);
}

static struct Sexpr * shift_expr(struct HashTable *env, const char *op, int num_bits)
{
    struct Sexpr *result = NULL;

    for (int count = num_bits - 1; count >= 0; --count) {
        uint64_t power = (uint64_t)1 << (uint64_t)count;

        char count_str[15];
        sprintf(count_str, "%d", count);
        char power_str[30];
        sprintf(power_str, "%" PRIu64, power);

        struct Sexpr * expr;
        if (count == 0) {
            expr = make_string_sexpr("x");
        } else {
            expr = make_list3_sexpr(make_string_sexpr(op),
                                    make_string_sexpr("x"),
                                    make_string_sexpr(power_str));
        }

        if (result == NULL) {
            result = expr;
        } else {
            result = make_list4_sexpr(make_string_sexpr("ite"),
                                      make_list3_sexpr(make_string_sexpr("="),
                                                       make_string_sexpr("y"),
                                                       make_string_sexpr(count_str)),
                                      expr,
                                      result);
        }
    }

    return result;
}

static void shift(struct HashTable *env, const char *type, int num_bits, bool left)
{
    // (define-fun $shl_i8 ((x Int) (y Int)) Int
    //  (ite (= 0 y) x
    //   (ite (= 1 y) (* x 2)
    //    (ite (= 2 y) (* x 4)
    //     ... )

    char name[20];
    sprintf(name, "$sh%s_%s", left ? "l" : "r", type);

    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Int"),
                                          shift_expr(env, left ? "*" : "div", num_bits));

    add_fol_helper(env, name, decl, NULL);
}

static void can_shr(struct HashTable *env, const char *type, int num_bits)
{
    // (and (<= 0 y) (< y num_bits))
    char txt[10];
    sprintf(txt, "%d", num_bits);
    struct Sexpr *expr =
        make_list3_sexpr(make_string_sexpr("and"),
                         make_list3_sexpr(make_string_sexpr("<="),
                                          make_string_sexpr("0"),
                                          make_string_sexpr("y")),
                         make_list3_sexpr(make_string_sexpr("<"),
                                          make_string_sexpr("y"),
                                          make_string_sexpr(txt)));

    // (define-fun $can_shr_u8 ((x Int) (y Int)) Bool expr)
    char name[20];
    sprintf(name, "$can_shr_%s", type);
    struct Sexpr *decl = make_list5_sexpr(make_string_sexpr("define-fun"),
                                          make_string_sexpr(name),
                                          xyInt(),
                                          make_string_sexpr("Bool"),
                                          expr);

    add_fol_helper(env, name, decl, NULL);
}

static void can_shl_i(struct HashTable *env, const char *type, const char *absmin, const char *max)
{
    // (define-fun $can_shl_i8 ((x Int) (y Int)) Bool
    //  (and ($can_shr_i8 x y)
    //   (and (<= (- 128) ($shl_i8 x y))
    //        (<= ($shl_i8 x y) 127))))

    char can_shl_name[20];
    sprintf(can_shl_name, "$can_shl_%s", type);

    char can_shr_name[20];
    sprintf(can_shr_name, "$can_shr_%s", type);

    char shl_name[20];
    sprintf(shl_name, "$shl_%s", type);

    struct Sexpr *decl =
        make_list5_sexpr(
            make_string_sexpr("define-fun"),
            make_string_sexpr(can_shl_name),
            xyInt(),
            make_string_sexpr("Bool"),
            make_list3_sexpr(
                make_string_sexpr("and"),
                make_list3_sexpr(
                    make_string_sexpr(can_shr_name),
                    make_string_sexpr("x"),
                    make_string_sexpr("y")),
                binop_minmax_check(shl_name, absmin, max)));

    add_fol_helper(env, can_shl_name, decl, NULL);
}

static void can_shl_u(struct HashTable *env, const char *type, const char *max)
{
    // (define-fun $can_shl_u8 ((x Int) (y Int)) Bool
    //  (and ($can_shr_u8 x y) (<= ($shl_u8 x y) 255))

    char can_shl_name[20];
    sprintf(can_shl_name, "$can_shl_%s", type);

    char can_shr_name[20];
    sprintf(can_shr_name, "$can_shr_%s", type);

    char shl_name[20];
    sprintf(shl_name, "$shl_%s", type);

    struct Sexpr *decl =
        make_list5_sexpr(
            make_string_sexpr("define-fun"),
            make_string_sexpr(can_shl_name),
            xyInt(),
            make_string_sexpr("Bool"),
            make_list3_sexpr(
                make_string_sexpr("and"),
                make_list3_sexpr(
                    make_string_sexpr(can_shr_name),
                    make_string_sexpr("x"),
                    make_string_sexpr("y")),
                binop_max_check(shl_name, max)));

    add_fol_helper(env, can_shl_name, decl, NULL);
}

static void can_neg_i(struct HashTable *env, const char *type, const char *absmin)
{
    // (define-fun $can_neg_i8 ((x Int)) Bool
    //  (distinct x (- 128)))

    char name[20];
    sprintf(name, "$can_neg_%s", type);

    struct Sexpr *decl = make_list5_sexpr(
        make_string_sexpr("define-fun"),
        make_string_sexpr(name),
        make_list1_sexpr( xInt() ),
        make_string_sexpr("Bool"),
        make_list3_sexpr(
            make_string_sexpr("distinct"),
            make_string_sexpr("x"),
            make_list2_sexpr(
                make_string_sexpr("-"),
                make_string_sexpr(absmin))));

    add_fol_helper(env, name, decl, NULL);
}

static void in_range_i(struct HashTable *env, const char *type, const char *absmin, const char *max)
{
    // (define-fun $in_range_u8 ((x Int)) Bool
    //  (and (<= 0 x) (<= x 255)))

    char name[20];
    sprintf(name, "$in_range_%s", type);

    struct Sexpr *decl = make_list5_sexpr(
        make_string_sexpr("define-fun"),
        make_string_sexpr(name),
        make_list1_sexpr( xInt() ),
        make_string_sexpr("Bool"),
        x_minmax_check(make_list2_sexpr( make_string_sexpr("-"), make_string_sexpr(absmin) ),
                       max));

    add_fol_helper(env, name, decl, NULL);
}

static void complement(struct HashTable *env, const char *type, const char *umax)
{
    // (define-fun $cpl_u8 ((x Int)) Int (- 255 x))
    // (define-fun $cpl_i8 ((x Int)) Int (- (- x) 1))

    char name[20];
    sprintf(name, "$cpl_%s", type);

    struct Sexpr *expr;
    if (umax) {
        expr = make_list3_sexpr(make_string_sexpr("-"),
                                make_string_sexpr(umax),
                                make_string_sexpr("x"));
    } else {
        expr = make_list3_sexpr(make_string_sexpr("-"),
                                make_list2_sexpr(make_string_sexpr("-"),
                                                 make_string_sexpr("x")),
                                make_string_sexpr("1"));
    }

    struct Sexpr *decl = make_list5_sexpr(
        make_string_sexpr("define-fun"),
        make_string_sexpr(name),
        make_list1_sexpr( xInt() ),
        make_string_sexpr("Int"),
        expr);

    add_fol_helper(env, name, decl, NULL);
}

static void add_integer_types(struct HashTable *verifier_env)
{
    const char * types[] = { "u8", "i8", "u16", "i16", "u32", "i32", "u64", "i64" };
    const char * unsigned_limits[] = { "255", "65535", "4294967295", "18446744073709551615" };
    const char * signed_limits[] = { "128", "127",
                                     "32768", "32767",
                                     "2147483648", "2147483647",
                                     "9223372036854775808", "9223372036854775807" };

    const char **t = types;
    const char **ulim = unsigned_limits;
    const char **slim = signed_limits;

    for (int i = 0; i < 4; ++i) {
        can_add_u(verifier_env, t[0], ulim[0]);
        can_add_i(verifier_env, t[1], slim[0], slim[1]);

        can_sub_u(verifier_env, t[0]);
        can_sub_i(verifier_env, t[1], slim[0], slim[1]);

        can_mul_u(verifier_env, t[0], ulim[0]);
        can_mul_i(verifier_env, t[1], slim[0], slim[1]);

        can_div_u(verifier_env, t[0]);
        can_div_i(verifier_env, t[1], slim[0]);
        div_i(verifier_env, t[1]);
        mod_i(verifier_env, t[1]);

        can_neg_i(verifier_env, t[1], slim[0]);

        in_range_u(verifier_env, t[0], ulim[0]);
        in_range_i(verifier_env, t[1], slim[0], slim[1]);

        int num_bits = 8 * (1 << i);

        bitwise(verifier_env, "and", true,  num_bits);
        bitwise(verifier_env, "or",  true,  num_bits);
        bitwise(verifier_env, "xor", true,  num_bits);
        bitwise(verifier_env, "and", false, num_bits);
        bitwise(verifier_env, "or",  false, num_bits);
        bitwise(verifier_env, "xor", false, num_bits);

        can_shl_u(verifier_env, t[0], ulim[0]);
        can_shl_i(verifier_env, t[1], slim[0], slim[1]);
        can_shr(verifier_env, t[0], num_bits);
        can_shr(verifier_env, t[1], num_bits);
        shift(verifier_env, t[0], num_bits, true);
        shift(verifier_env, t[1], num_bits, true);
        shift(verifier_env, t[0], num_bits, false);
        shift(verifier_env, t[1], num_bits, false);

        complement(verifier_env, t[0], ulim[0]);
        complement(verifier_env, t[1], NULL);

        t += 2;
        ulim += 1;
        slim += 2;
    }

    div_i(verifier_env, "int");
    mod_i(verifier_env, "int");
}

static void setup_arbitrary_array(struct VerifierEnv *verifier_env)
{
    struct Sexpr *array_type = make_list3_sexpr(
        make_string_sexpr("Array"),
        make_string_sexpr("IDX"),
        make_string_sexpr("ELT"));

    struct Sexpr *arbitrary_elt = make_string_sexpr("$ARBITRARY");
    make_instance(&arbitrary_elt, make_list1_sexpr(make_string_sexpr("ELT")));

    add_fol_helper(
        verifier_env->table,
        "$ARBITRARY-ARRAY",

        make_list4_sexpr(
            make_string_sexpr("generic"),
            make_string_sexpr("$ARBITRARY-ARRAY"),
            make_list2_sexpr(make_string_sexpr("IDX"),
                             make_string_sexpr("ELT")),
            make_list3_sexpr(
                make_string_sexpr("declare-const"),
                make_string_sexpr("$ARBITRARY-ARRAY"),
                copy_sexpr(array_type))),

        make_list1_sexpr(
            make_list4_sexpr(
                make_string_sexpr("generic"),
                make_string_sexpr("$ARBITRARY-ARRAY"),
                make_list2_sexpr(make_string_sexpr("IDX"),
                                 make_string_sexpr("ELT")),
                make_list2_sexpr(
                    make_string_sexpr("assert"),
                    make_list3_sexpr(
                        make_string_sexpr("forall"),
                        make_list1_sexpr(
                            make_list2_sexpr(
                                make_string_sexpr("idx"),
                                make_string_sexpr("IDX"))),
                        make_list3_sexpr(
                            make_string_sexpr("="),
                            make_list3_sexpr(
                                make_string_sexpr("select"),
                                make_string_sexpr("$ARBITRARY-ARRAY"),
                                make_string_sexpr("idx")),
                            arbitrary_elt))))));
    arbitrary_elt = NULL;

    free_sexpr(array_type);
    array_type = NULL;
}

void setup_initial_verifier_env(struct VerifierEnv *verifier_env)
{
    add_integer_types(verifier_env->table);

    // $ARBITRARY
    add_fol_helper(
        verifier_env->table,
        "$ARBITRARY",
        make_list4_sexpr(
            make_string_sexpr("generic"),
            make_string_sexpr("$ARBITRARY"),
            make_list1_sexpr(make_string_sexpr("T")),
            make_list3_sexpr(
                make_string_sexpr("declare-const"),
                make_string_sexpr("$ARBITRARY"),
                make_string_sexpr("T"))),
        NULL);

    // $ARBITRARY-ARRAY
    setup_arbitrary_array(verifier_env);

    // (instance $PROD (tyargs)) is handled by the generic system, but
    // need to add "$PROD" (with no tyargs) as a special case
    add_fol_helper(
        verifier_env->table,
        "$PROD",
        make_list3_sexpr(
            make_string_sexpr("declare-datatypes"),
            make_list1_sexpr(
                make_list2_sexpr(
                    make_string_sexpr("$PROD"),
                    make_string_sexpr("0"))),
            make_list1_sexpr(  // 1 type being defined
                make_list1_sexpr(    // 1 variant
                    make_list1_sexpr(     // variant is list of name then fields
                        make_string_sexpr("$PROD"))))),    // (just name in this case)
        NULL);
}

bool import_builtin_module(const char *name,
                           struct HashTable *renamer_env,
                           struct HashTable *type_env,
                           struct VerifierEnv *verifier_env,
                           struct HashTable *codegen_env)
{
    if (strcmp(name, "Int") == 0) {
        // Built-in "Int" module

        struct NameList *all_names = NULL;

        const char *funs[] = { "add", "sub", "mul", "div" };
        const int sizes[] = { 8, 16, 32, 64 };

        for (unsigned int i = 0; i < sizeof(funs)/sizeof(funs[0]); ++i) {
            for (unsigned int j = 0; j < sizeof(sizes)/sizeof(sizes[0]); ++j) {
                for (int s = 0; s < 2; ++s) {

                    char buf[100];
                    sprintf(buf, "%%Int.can_%s_%s%d", funs[i], s ? "i" : "u", sizes[j]);

                    struct Type *fun_ty = make_type(g_no_location, TY_FUNCTION);
                    fun_ty->function_data.args = alloc(sizeof(struct FunArg));
                    fun_ty->function_data.args->name = NULL;
                    fun_ty->function_data.args->type = make_int_type(g_no_location, s, sizes[j]);
                    fun_ty->function_data.args->ref = false;
                    fun_ty->function_data.args->next = alloc(sizeof(struct FunArg));
                    fun_ty->function_data.args->next->name = NULL;
                    fun_ty->function_data.args->next->type = make_int_type(g_no_location, s, sizes[j]);
                    fun_ty->function_data.args->next->ref = false;
                    fun_ty->function_data.args->next->next = NULL;
                    fun_ty->function_data.return_type = make_type(g_no_location, TY_BOOL);

                    add_to_type_env(type_env, &buf[1], fun_ty, true, true, false, false);

                    struct Sexpr *fol_decl =
                        make_list5_sexpr(
                            make_string_sexpr("define-fun"),
                            make_string_sexpr(buf),
                            xyInt(),
                            make_string_sexpr("Bool"),
                            make_list3_sexpr(
                                make_string_sexpr_handover(copy_string_2("$", &buf[5])),
                                make_string_sexpr("x"),
                                make_string_sexpr("y")));

                    add_fol_helper(verifier_env->table, buf, fol_decl, NULL);

                    struct NameList *node = alloc(sizeof(struct NameList));
                    node->name = copy_string(&buf[5]);
                    node->next = all_names;
                    all_names = node;
                }
            }
        }

        hash_table_insert(renamer_env, copy_string("Int"), all_names);

        return true;

    } else {
        return false;
    }
}
