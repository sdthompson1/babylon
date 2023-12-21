/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"
#include "fol.h"
#include "hash_table.h"
#include "scc.h"
#include "sexpr.h"
#include "util.h"
#include "verifier.h"
#include "verifier_context.h"
#include "verifier_dependency.h"
#include "verifier_run.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static struct Sexpr * make_fol_problem(const struct HashTable *global_env,
                                       const struct HashTable *local_env,
                                       struct Sexpr *initial_asserts,
                                       struct Sexpr *conjecture)
{
    struct Sexpr *first = NULL;
    struct Sexpr *last = NULL;

    struct Component * component =
        get_sexpr_dependencies(global_env,
                               local_env,
                               initial_asserts,
                               conjecture);

    while (component) {

        struct ComponentVertex *vertex = component->first_vertex;
        while (vertex) {
            const char *name = vertex->vertex_data;

            struct Item *item = hash_table_lookup(local_env, name);
            if (item == NULL) {
                item = hash_table_lookup(global_env, name);
            }

            if (item->fol_decl) {
                struct Sexpr *new_decl = make_pair_sexpr(copy_sexpr(item->fol_decl), NULL);
                if (last) {
                    last->right = new_decl;
                } else {
                    first = new_decl;
                }
                last = new_decl;
            }

            for (struct Sexpr* assrt = item->fol_axioms; assrt; assrt = assrt->right) {
                struct Sexpr *new_assert = make_pair_sexpr(copy_sexpr(assrt->left), NULL);
                if (last) {
                    last->right = new_assert;
                } else {
                    first = new_assert;
                }
                last = new_assert;
            }

            struct ComponentVertex *to_free = vertex;
            vertex = vertex->next;
            free(to_free);
        }

        struct Component *to_free = component;
        component = component->next_component;
        free(to_free);
    }

    // append initial_asserts
    if (last) {
        last->right = copy_sexpr(initial_asserts);
    } else {
        first = copy_sexpr(initial_asserts);
        last = first;
    }
    while (last && last->right) {
        last = last->right;
    }

    // append 'prove' command
    struct Sexpr *prove =
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr("prove"),
                copy_sexpr(conjecture)));
    if (last) {
        last->right = prove;
    } else {
        last = prove;
    }
    last = prove;

    return first;
}

const char * make_debug_filename(struct VContext *context,
                                 struct Location location)
{
    if (!context->debug_filename_prefix) {
        return NULL;
    }

    for (int num = 0; num < 100000; ++num) {
        char tail[100];
        sprintf(tail, ".%d.%d", location.begin_line_num, num);

        char *name = copy_string_2(context->debug_filename_prefix, tail);
        if (!hash_table_contains_key(context->debug_files_created, name)) {
            hash_table_insert(context->debug_files_created, name, NULL);
            return name;
        }

        free(name);
    }

    return NULL;
}

bool verify_condition(struct VContext *context,
                      struct Location location,
                      struct Sexpr *condition,
                      const char *msg)
{
    if (context->interface_only) {
        return true;
    }

    if (!context->continue_after_error && context->error_found) {
        return true;
    }

    const char *debug_filename = make_debug_filename(context, location);

    // Progress message (TODO: show secondary location?)
    if (context->show_progress) {
        char buf[512];
        format_location(&location, true, false, buf, sizeof(buf));
        fprintf(stderr, "Checking %s", buf);
        if (msg) {
            fprintf(stderr, " (%s)", msg);
        }
        if (debug_filename) {
            fprintf(stderr, " (%s.smt)", debug_filename);
        }
        fprintf(stderr, " ");
    }

    // Make an "asserts" list out of the path condition and facts
    struct Sexpr *initial_asserts =
        make_list1_sexpr(make_list2_sexpr(make_string_sexpr("assert"),
                                          copy_sexpr(context->path_condition)));
    struct Sexpr **tail_ptr = &initial_asserts->right;

    for (struct Sexpr *fact_node = context->facts; fact_node; fact_node = fact_node->right) {
        *tail_ptr = make_list1_sexpr(make_list2_sexpr(make_string_sexpr("assert"),
                                                      copy_sexpr(fact_node->left)));
        tail_ptr = &((*tail_ptr)->right);
    }

    // Make the FOL problem
    struct Sexpr * problem = make_fol_problem(context->global_env,
                                              context->local_env,
                                              initial_asserts,
                                              condition);

    // Solve the FOL problem
    enum FolResult result = solve_fol_problem(problem,
                                              context->cache_prefix,
                                              debug_filename,
                                              context->show_progress,
                                              context->timeout_seconds);

    free_sexpr(initial_asserts);

    if (result != FOL_RESULT_PROVED) {
        context->error_found = true;
    }

    return result == FOL_RESULT_PROVED;
}
