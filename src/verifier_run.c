/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

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
                                       const struct HashTable *local_hidden,
                                       struct Sexpr *initial_asserts,   // handover
                                       struct Sexpr *conjecture)
{
    // Add initial asserts and the 'prove' command.
    struct Sexpr *result = initial_asserts;
    struct Sexpr **tail_ptr = &result;
    while (*tail_ptr) {
        tail_ptr = &(*tail_ptr)->right;
    }
    *tail_ptr =
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr("prove"),
                copy_sexpr(conjecture)));

    // Add the required dependency definitions/axioms.
    return get_sexpr_dependencies(global_env, local_env, local_hidden,
                                  result, result);
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

void verify_condition(struct VContext *context,
                      struct Location location,
                      struct Sexpr *condition,   // NOT handed over
                      const char *description,   // NOT handed over
                      const char *error_msg)     // handover
{
    if (context->interface_only) {
        free((char*)error_msg);
        return;
    }

    if (!fol_continue_after_error() && context->error_found) {
        free((char*)error_msg);
        return;
    }

    const char *debug_filename = make_debug_filename(context, location);

    // Progress message (TODO: show secondary location?)
    char buf[512];
    format_location(&location, true, false, buf, sizeof(buf));
    char *full_description = copy_string_2("Checking ", buf);
    if (description) {
        char *full_desc_new = copy_string_4(full_description, " (", description, ")");
        free(full_description);
        full_description = full_desc_new;
    }
    if (debug_filename) {
        char *full_desc_new = copy_string_4(full_description, " (", debug_filename, ".smt)");
        free(full_description);
        full_description = full_desc_new;
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
                                              context->local_hidden,
                                              initial_asserts,
                                              condition);

    // Send the FOL problem for solving.
    solve_fol_problem(problem,  // handover
                      context->show_progress,
                      full_description,   // handover
                      error_msg,     // handover
                      debug_filename);

    // Update context->error_found if required.
    // Note: solve_fol_problem has already called update_fol_status, so we just need
    // to call fol_error_found here.
    context->error_found = fol_error_found();
}
