/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "cprint.h"
#include "error.h"
#include "size_expr.h"
#include "util.h"

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>


// A "Term" is either a positive integer, or a positive integer
// multiplied by a variable.
// Examples: 16, 4*a, 7*b.

// Invariants: multiplier is always nonzero.

// A "TermList" represents a sum of terms.
// Example: 3 + 6*a + 4*b.

// Invariants: The list is kept sorted by varname (with NULL, if
// present, being first). No duplicate varnames are present.

struct SizeTermList {
    char *varname;         // NULL if the term is constant
    uint64_t multiplier;
    struct SizeTermList *next;
};


// A "SizeExpr" is the maximum of several TermLists.
// Example: max(6, 2 + 4*a, 7*b).
// An empty list is also valid (and represents zero).

// Invariants: There are no "redundant" term-lists present.
// For example max(4*a+b, 3*a+b) is illegal because the 3*a+b
// is redundant, it will always be <= 4*a+b (recall our
// assumption that variables always have non-negative values),
// so it can (and should) be omitted from the list.

// Note that an empty TermList would always be considered redundant,
// thus there should not be any NULL term_list pointers present.

struct SizeExpr {
    struct SizeTermList *term_list;
    struct SizeExpr *next;
};


static int varname_cmp(char *lhs, char *rhs)
{
    if (lhs == NULL) {
        if (rhs == NULL) {
            return 0;
        } else {
            return -1;
        }
    } else if (rhs == NULL) {
        return 1;
    } else {
        return strcmp(lhs, rhs);
    }
}

static void free_term_list(struct SizeTermList *list)
{
    while (list) {
        free(list->varname);
        struct SizeTermList *next = list->next;
        free(list);
        list = next;
    }
}

void free_size_expr(struct SizeExpr *expr)
{
    while (expr) {
        free_term_list(expr->term_list);
        struct SizeExpr *next = expr->next;
        free(expr);
        expr = next;
    }
}


static struct SizeTermList * copy_term_list(struct SizeTermList *list)
{
    struct SizeTermList *output = NULL;
    struct SizeTermList **tail = &output;

    while (list) {
        *tail = alloc(sizeof(struct SizeTermList));
        (*tail)->varname = list->varname ? copy_string(list->varname) : NULL;
        (*tail)->multiplier = list->multiplier;
        (*tail)->next = NULL;
        tail = &(*tail)->next;
        list = list->next;
    }

    return output;
}

struct SizeExpr * copy_size_expr(struct SizeExpr *expr)
{
    struct SizeExpr *output = NULL;
    struct SizeExpr **tail = &output;

    while (expr) {
        *tail = alloc(sizeof(struct SizeExpr));
        (*tail)->term_list = copy_term_list(expr->term_list);
        (*tail)->next = NULL;
        tail = &(*tail)->next;
        expr = expr->next;
    }

    return output;
}


struct SizeExpr * zero_size_expr()
{
    return NULL;
}

struct SizeExpr * const_size_expr(uint64_t value)
{
    return var_size_expr(NULL, value);
}

struct SizeExpr * var_size_expr(const char *varname, uint64_t multiplier)
{
    if (multiplier == 0) {
        // Special case
        return NULL;
    }

    struct SizeTermList *term_list = alloc(sizeof(struct SizeTermList));
    term_list->varname = varname ? copy_string(varname) : NULL;
    term_list->multiplier = multiplier;
    term_list->next = NULL;

    struct SizeExpr *expr = alloc(sizeof(struct SizeExpr));
    expr->term_list = term_list;
    expr->next = NULL;

    return expr;
}


static struct SizeTermList * add_term_lists(struct SizeTermList *lhs, struct SizeTermList *rhs)
{
    struct SizeTermList *output = NULL;
    struct SizeTermList **tail = &output;

    while (lhs || rhs) {
        *tail = alloc(sizeof(struct SizeTermList));
        (*tail)->next = NULL;

        int cmp;
        if (lhs == NULL) {
            cmp = 1;
        } else if (rhs == NULL) {
            cmp = -1;
        } else {
            cmp = varname_cmp(lhs->varname, rhs->varname);
        }

        if (cmp > 0) {
            // rhs is the earlier in the list, so take from the rhs
            (*tail)->varname = rhs->varname ? copy_string(rhs->varname) : NULL;
            (*tail)->multiplier = rhs->multiplier;
            rhs = rhs->next;

        } else if (cmp < 0) {
            // lhs is the earlier in the list, so take from the lhs
            (*tail)->varname = lhs->varname ? copy_string(lhs->varname) : NULL;
            (*tail)->multiplier = lhs->multiplier;
            lhs = lhs->next;

        } else {
            // sum the two terms
            (*tail)->varname = lhs->varname ? copy_string(lhs->varname) : NULL;
            (*tail)->multiplier = lhs->multiplier + rhs->multiplier;
            lhs = lhs->next;
            rhs = rhs->next;
        }

        tail = &(*tail)->next;
    }

    return output;
}


// returns true if the lhs is always <= the rhs no matter the variable values
static bool term_list_smaller_or_equal(struct SizeTermList *lhs, struct SizeTermList *rhs)
{
    while (lhs || rhs) {
        if (rhs == NULL) {
            // terms exist on the lhs, without a counterpart on the rhs.
            // the lhs cannot be smaller.
            return false;
        }

        if (lhs == NULL) {
            // there are extra terms on the rhs, but these correspond to zero on
            // the lhs, so the lhs is definitely smaller (or equal).
            return true;
        }

        int cmp = varname_cmp(lhs->varname, rhs->varname);

        if (cmp < 0) {
            // lhs has a variable that's missing from the rhs, so
            // the lhs cannot be smaller
            return false;
        }

        if (cmp > 0) {
            // rhs has a variable that's missing from the lhs, so
            // lhs is definitely smaller or equal, so far
            rhs = rhs->next;

        } else {
            // we have to check the multipliers
            if (lhs->multiplier > rhs->multiplier) {
                // the lhs can be bigger, if this variable is nonzero (and large enough)
                return false;
            }
            lhs = lhs->next;
            rhs = rhs->next;
        }
    }

    return true;
}

// Convert an "improper" SizeExpr (one with redundant TermLists, but otherwise valid)
// into a fully valid SizeExpr, by removing any redundant TermLists present.
static void remove_redundancy(struct SizeExpr **expr)
{
    // Check each pair of TermLists.
    // If one is <= the other, then set the <= one to NULL (temporarily).
    // Afterwards we will separately sweep through the list removing NULLs.
    for (struct SizeExpr *e1 = *expr; e1; e1 = e1->next) {
        for (struct SizeExpr *e2 = *expr; e2; e2 = e2->next) {
            if (e1 != e2 && e1->term_list != NULL && e2->term_list != NULL) {
                if (term_list_smaller_or_equal(e1->term_list, e2->term_list)) {
                    free_term_list(e1->term_list);
                    e1->term_list = NULL;
                }
            }
        }
    }

    struct SizeExpr **ptr = expr;
    while (*ptr) {
        if ((*ptr)->term_list == NULL) {
            struct SizeExpr *next = (*ptr)->next;
            free(*ptr);
            *ptr = next;
        } else {
            ptr = &(*ptr)->next;
        }
    }
}


struct SizeExpr * add_size_expr(struct SizeExpr *lhs, struct SizeExpr *rhs)
{
    // If one of the lists is zero, just return the other.
    if (lhs == NULL) {
        return copy_size_expr(rhs);

    } else if (rhs == NULL) {
        return copy_size_expr(lhs);

    } else {
        // Add all possible pairs of TermLists.
        // For example, max(a, b+c) + max(x, y) = max(a+x, a+y, b+c+x, b+c+y).

        struct SizeExpr *output = NULL;
        struct SizeExpr **tail = &output;

        for (struct SizeExpr *e1 = lhs; e1; e1 = e1->next) {
            for (struct SizeExpr *e2 = rhs; e2; e2 = e2->next) {
                *tail = alloc(sizeof(struct SizeExpr));
                (*tail)->term_list = add_term_lists(e1->term_list, e2->term_list);
                (*tail)->next = NULL;
                tail = &(*tail)->next;
            }
        }

        // The above might have created redundancy.
        // For example, max(4, a) + max(3, a) = max(7, 4 + a, 3 + a, 2*a).
        // This is better expressed as max(7, 4 + a, 2*a).
        // Call remove_redundancy to deal with this.
        remove_redundancy(&output);

        return output;
    }
}

struct SizeExpr * multiply_size_expr(uint64_t lhs, struct SizeExpr *rhs)
{
    // If either factor is zero, the result is zero.
    if (lhs == 0 || rhs == NULL) {
        return NULL;
    }

    // Just multiply each TermList by the lhs.
    struct SizeExpr *output = NULL;
    struct SizeExpr **output_tail = &output;

    for (struct SizeExpr *e = rhs; e; e = e->next) {
        struct SizeTermList *list = NULL;
        struct SizeTermList **list_tail = &list;

        for (struct SizeTermList *x = e->term_list; x; x = x->next) {
            // multiply, checking for overflow
            uint64_t mult = lhs * x->multiplier;
            if (mult / lhs != x->multiplier) {
                fatal_error("array size too big");
            }

            struct SizeTermList *node = alloc(sizeof(struct SizeTermList));
            node->multiplier = mult;
            node->varname = x->varname ? copy_string(x->varname) : NULL;
            node->next = NULL;
            *list_tail = node;
            list_tail = &node->next;
        }

        struct SizeExpr *node = alloc(sizeof(struct SizeExpr));
        node->term_list = list;
        node->next = NULL;
        *output_tail = node;
        output_tail = &node->next;
    }

    return output;
}

struct SizeExpr * max_size_expr(struct SizeExpr *lhs, struct SizeExpr *rhs)
{
    // We can just concantenate the two lists, then remove any
    // resulting redundancy.
    struct SizeExpr *output = NULL;
    struct SizeExpr **tail = &output;

    for (struct SizeExpr *e = lhs; e; e = e->next) {
        *tail = alloc(sizeof(struct SizeExpr));
        (*tail)->term_list = copy_term_list(e->term_list);
        (*tail)->next = NULL;
        tail = &(*tail)->next;
    }

    for (struct SizeExpr *e = rhs; e; e = e->next) {
        *tail = alloc(sizeof(struct SizeExpr));
        (*tail)->term_list = copy_term_list(e->term_list);
        (*tail)->next = NULL;
        tail = &(*tail)->next;
    }

    remove_redundancy(&output);

    return output;
}

bool is_size_expr_const(struct SizeExpr *expr)
{
    if (expr == NULL) {
        // expr is 0
        return true;

    } else if (expr->next) {
        // expr is max(something, something) - cannot be const
        return false;

    } else if (expr->term_list->next) {
        // expr is something + something - cannot be const
        return false;

    } else {
        // expr is a single TermList containing a single Term
        // see if it is constant or variable
        return expr->term_list->varname == NULL;
    }
}

bool is_size_expr_zero(struct SizeExpr *expr)
{
    return expr == NULL;
}

uint64_t get_size_expr_const(struct SizeExpr *expr)
{
    if (expr == NULL) {
        return 0;
    } else {
        return expr->term_list->multiplier;
    }
}

static void write_term_list(struct CPrinter *pr,
                            struct SizeTermList *list)
{
    while (list) {
        char buf[30];
        sprintf(buf, "%" PRIu64, list->multiplier);
        if (list->varname == NULL) {
            print_token(pr, buf);
        } else {
            if (list->multiplier != 1) {
                print_token(pr, buf);
                print_token(pr, "*");
            }
            print_token(pr, list->varname);
        }
        if (list->next) print_token(pr, "+");
        list = list->next;
    }
}

void write_size_expr(struct CPrinter *pr,
                     struct SizeExpr *expr,
                     char * (*new_temp_name)(void *cxt),
                     void *cxt)
{
    if (expr && expr->next) {
        // need to use "max"...
        char *result_name = new_temp_name(cxt);
        begin_item(pr);
        print_token(pr, "uint64_t");
        print_token(pr, result_name);
        print_token(pr, "=");
        print_token(pr, "0");
        print_token(pr, ";");
        new_line(pr);
        end_item(pr);

        while (expr) {
            char *temp_name = new_temp_name(cxt);
            begin_item(pr);
            print_token(pr, "uint64_t");
            print_token(pr, temp_name);
            print_token(pr, "=");
            write_term_list(pr, expr->term_list);
            print_token(pr, ";");
            new_line(pr);

            print_token(pr, result_name);
            print_token(pr, "=");
            print_token(pr, temp_name);
            print_token(pr, ">");
            print_token(pr, result_name);
            print_token(pr, "?");
            print_token(pr, temp_name);
            print_token(pr, ":");
            print_token(pr, result_name);
            print_token(pr, ";");
            new_line(pr);
            end_item(pr);

            free(temp_name);
            expr = expr->next;
        }

        print_token(pr, result_name);
        free(result_name);

    } else if (expr) {
        write_term_list(pr, expr->term_list);

    } else {
        print_token(pr, "0");
    }
}
