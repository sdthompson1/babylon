/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"
#include "hash_table.h"
#include "remove_smt_shadowing.h"
#include "sexpr.h"
#include "util.h"

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>


// Data structures used:

// global_names = hash table mapping each known global name to the
// value NULL. (The name ptrs are not allocated; they point directly
// to the string in the declare-fun, or whatever.)

// local_names = Sexpr list, where each node in the list is itself a
// pair. The 'left' of this pair is an allocated copy of the local
// name, and the 'right' is a uintptr_t giving the "number" to use
// for this copy of the local.


// Given base_name and number, returns the "renamed" name.
// Returns a new string.
static char * make_name(const char *base_name, uintptr_t n)
{
    if (n == 0) {
        return copy_string(base_name);
    } else {
        char buf[50];
        sprintf(buf, "~%" PRIuPTR, n);
        return copy_string_2(base_name, buf);
    }
}

// Scan a top-level expr to see if it is something like declare-fun
// that creates global name(s). If so, add the names to the hash table.
static void add_global_names(struct HashTable *global_names,
                             struct Sexpr *expr)
{
    // Expecting (cmdname args...)
    if (expr == NULL || expr->type != S_PAIR
    || expr->left == NULL || expr->left->type != S_STRING) {
        fatal_error("SMT-LIB command not of expected form");
    }

    const char *cmd = expr->left->string;

    // Most cmds are of the form (declare-something Name ...).
    // We need to add the "Name" to global_names.
    if (strcmp(cmd, "declare-sort") == 0
    || strcmp(cmd, "declare-const") == 0
    || strcmp(cmd, "declare-fun") == 0
    || strcmp(cmd, "define-fun") == 0) {
        if (expr->right->left != NULL && expr->right->left->type == S_STRING) {
            hash_table_insert(global_names, expr->right->left->string, NULL);
        }
        return;
    }

    // declare-datatypes is a bit more complicated!
    if (strcmp(cmd, "declare-datatypes") == 0) {
        // (We assume the syntax is correct here, without checking)
        struct Sexpr *sort_decs = expr->right->left;
        struct Sexpr *datatype_decs = expr->right->right->left;

        // Iterate through sort-decs
        // Each sort-dec is a name and number, e.g. (Tree 1)
        for (struct Sexpr *node = sort_decs; node; node = node->right) {
            hash_table_insert(global_names, node->left->left->string, NULL);
        }

        // Iterate through datatype-decs
        for (struct Sexpr *outer_node = datatype_decs; outer_node; outer_node = outer_node->right) {
            // outer_node->left is itself a list of ctor-decs
            for (struct Sexpr *inner_node = outer_node->left; inner_node; inner_node = inner_node->right) {
                // inner_node->left is a list of the form: (Ctorname ARGS)
                // So inner_node->left->left is the Ctorname
                hash_table_insert(global_names, inner_node->left->left->string, NULL);
                // Then inner_node->left->right is a list of fields
                for (struct Sexpr *field_node = inner_node->left->right; field_node; field_node = field_node->right) {
                    // field_node->left is something like (fieldname Int)
                    // So field_node->left->left is the name.
                    hash_table_insert(global_names, field_node->left->left->string, NULL);
                }
            }
        }
    }
}

// Hand over a string representing a newly bound local variable name.
// Return a new string to replace it with, and also add an entry to
// the head of the local_names list.
static char * add_local_name(struct HashTable *global_names,
                             struct Sexpr **local_names,
                             const char *name)
{
    // Generate a number.
    // This will be the existing number plus one if the name is
    // already in local_names; or 1 if the name shadows a global
    // name; or 0 otherwise.

    uintptr_t n;

    // See if we already have this in local_names.
    bool found_local = false;
    for (struct Sexpr *node = *local_names; node; node = node->right) {
        if (strcmp(node->left->left->string, name) == 0) {
            n = (uintptr_t) node->left->right;
            ++n;
            found_local = true;
            break;
        }
    }

    if (!found_local) {
        n = hash_table_contains_key(global_names, name) ? 1 : 0;
    }

    // Now make a new node in the local_names list.
    struct Sexpr *name_node = alloc(sizeof(struct Sexpr));
    name_node->type = S_STRING;
    name_node->string = name;

    struct Sexpr *pair = alloc(sizeof(struct Sexpr));
    pair->type = S_PAIR;
    pair->left = name_node;
    pair->right = (struct Sexpr*) n;

    struct Sexpr *node = alloc(sizeof(struct Sexpr));
    node->type = S_PAIR;
    node->left = pair;
    node->right = *local_names;
    *local_names = node;

    // Return the new name.
    return make_name(name, n);
}

static void remove_shadowing(struct HashTable *global_names,
                             struct Sexpr **local_names,
                             struct Sexpr *expr);

static void pop_local_name(struct Sexpr **local_names)
{
    free((void*)((*local_names)->left->left->string));
    free((*local_names)->left->left);
    free((*local_names)->left);
    struct Sexpr *next = (*local_names)->right;
    free(*local_names);
    *local_names = next;
}

static void remove_shadowing_from_let(struct HashTable *global_names,
                                      struct Sexpr **local_names,
                                      struct Sexpr *let_expr)
{
    for (struct Sexpr *node = let_expr->right->left; node; node = node->right) {
        // remove shadowing from "rhs" of each let (note: the new vars are not in scope for this)
        remove_shadowing(global_names, local_names, node->left->right->left);
    }

    for (struct Sexpr *node = let_expr->right->left; node; node = node->right) {
        // add the new vars to scope
        node->left->left->string = add_local_name(global_names, local_names, node->left->left->string);
    }

    // remove shadowing from the "body" of the let
    remove_shadowing(global_names, local_names, let_expr->right->right->left);

    // remove the new vars from scope again
    for (struct Sexpr *node = let_expr->right->left; node; node = node->right) {
        pop_local_name(local_names);
    }
}

static void remove_shadowing_from_match(struct HashTable *global_names,
                                        struct Sexpr **local_names,
                                        struct Sexpr *match_expr)
{
    // match_expr->right->left is the scrutinee
    remove_shadowing(global_names, local_names, match_expr->right->left);

    // match_expr->right->right->left is a list of "arms"
    for (struct Sexpr *arm_node = match_expr->right->right->left; arm_node; arm_node = arm_node->right) {

        // An arm is (pattern rhs)
        struct Sexpr *pat = arm_node->left->left;

        // A pattern is either a string (variable name) or
        // a pair (CtorName VarNames...).
        if (pat->type == S_STRING) {
            pat->string = add_local_name(global_names, local_names, pat->string);
        } else {
            for (struct Sexpr *varlist = pat->right; varlist; varlist = varlist->right) {
                varlist->left->string = add_local_name(global_names, local_names, varlist->left->string);
            }
        }

        // arm_node->left->right->left is the "rhs" of the arm
        remove_shadowing(global_names, local_names, arm_node->left->right->left);

        // Remove the new variables from scope again
        if (pat->type == S_STRING) {
            pop_local_name(local_names);
        } else {
            for (struct Sexpr *varlist = pat->right; varlist; varlist = varlist->right) {
                pop_local_name(local_names);
            }
        }
    }
}

// This modifies 'expr' in place (any strings that need to be
// renamed are freed and reallocated).
static void remove_shadowing(struct HashTable *global_names,
                             struct Sexpr **local_names,
                             struct Sexpr *expr)
{
    if (expr == NULL) {
        return;
    }

    if (expr->type == S_PAIR) {
        // Look for (forall ...) or (exists ...) or (let ...) or (match ...)

        if (expr->left && expr->left->type == S_STRING) {
            if (strcmp(expr->left->string, "forall") == 0
            || strcmp(expr->left->string, "exists") == 0
            || strcmp(expr->left->string, "let") == 0) {
                remove_shadowing_from_let(global_names, local_names, expr);
                return;
            }
            if (strcmp(expr->left->string, "match") == 0) {
                remove_shadowing_from_match(global_names, local_names, expr);
                return;
            }
        }

        // If we get here, it is just a normal pair. Recursively update
        // the "left" and "right" subexpressions.

        remove_shadowing(global_names, local_names, expr->left);
        remove_shadowing(global_names, local_names, expr->right);
        return;
    }

    // It must be S_STRING.
    // If it begins "%" or "$" then it could be a local name that
    // needs renaming.
    if (expr->string[0] == '%' || expr->string[0] == '$') {
        for (struct Sexpr *node = *local_names; node; node = node->right) {
            if (strcmp(node->left->left->string, expr->string) == 0) {
                // Found!
                // Replace the string in-place.
                free((void*)expr->string);
                expr->string = make_name(node->left->left->string, (uintptr_t)node->left->right);
                return;
            }
        }
    }

    // If we get here, no changes are needed.
}

// This modifies 'expr' in place.
void remove_smt_shadowing(struct Sexpr *expr)
{
    struct HashTable *global_names = new_hash_table();
    struct Sexpr *local_names = NULL;

    for (struct Sexpr *node = expr; node; node = node->right) {
        add_global_names(global_names, node->left);
        remove_shadowing(global_names, &local_names, node->left);
    }

    free_hash_table(global_names);
}
