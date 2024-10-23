/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "fol.h"
#include "hash_table.h"
#include "initial_env.h"
#include "sha256.h"
#include "stacked_hash_table.h"
#include "util.h"
#include "verifier.h"
#include "verifier_context.h"
#include "verifier_decls.h"

#include <stdlib.h>
#include <string.h>

struct VerifierEnv * new_verifier_env()
{
    struct VerifierEnv *env = alloc(sizeof(struct VerifierEnv));

    env->stack = alloc(sizeof(struct StackedHashTable));
    env->stack->table = new_hash_table();
    env->stack->base = NULL;

    env->string_names = new_hash_table();
    setup_initial_verifier_env(env);
    return env;
}

void free_verifier_env(struct VerifierEnv *env)
{
    while (env->stack) {
        env->stack = pop_verifier_stack(env->stack);
    }

    if (!hash_table_empty(env->string_names)) {
        fatal_error("string_names wasn't cleared between decls");
    }
    free_hash_table(env->string_names);

    free(env);
}

void push_verifier_env(struct VerifierEnv *env)
{
    env->stack = push_verifier_stack(env->stack);
}

void pop_verifier_env(struct VerifierEnv *env)
{
    env->stack = pop_verifier_stack(env->stack);
}

void collapse_verifier_env(struct VerifierEnv *env)
{
    env->stack = collapse_verifier_stack(env->stack);
}

struct HashTable * detach_verifier_env_layer(struct VerifierEnv *env)
{
    struct HashTable * layer = env->stack->table;
    struct StackedHashTable * base = env->stack->base;
    free(env->stack);
    env->stack = base;
    return layer;
}

void attach_verifier_env_layer(struct VerifierEnv *env, struct HashTable *layer)
{
    struct StackedHashTable * node = alloc(sizeof(struct StackedHashTable));
    node->table = layer;
    node->base = env->stack;
    env->stack = node;
}

bool verify_module(struct VerifierEnv *verifier_env,
                   struct Module *module,
                   struct VerifierOptions *options)
{
    struct VContext cxt;
    cxt.stack = verifier_env->stack;
    cxt.local_to_version = new_hash_table();
    cxt.local_counter = new_hash_table();
    cxt.string_names = verifier_env->string_names;
    cxt.current_decl_name = NULL;
    cxt.refs = new_hash_table();
    cxt.new_values = NULL;
    cxt.path_condition = NULL;
    cxt.facts = NULL;
    cxt.num_facts = 0;
    cxt.run_solver = false;  // set properly below
    cxt.function_args = NULL;
    cxt.arglist_sexpr = cxt.funapp_sexpr = NULL;
    cxt.postconds = NULL;
    cxt.assert_exprs = NULL;
    cxt.show_progress = options->show_progress;
    cxt.error_found = fol_error_found();
    cxt.local_hidden = new_hash_table();

    cxt.debug_filename_prefix = options->debug_filename_prefix;
    if (cxt.debug_filename_prefix) {
        cxt.debug_files_created = new_hash_table();
    } else {
        cxt.debug_files_created = NULL;
    }

    cxt.cache_db = options->cache_db;

    // Verify each decl in the interface
    cxt.run_solver = options->mode == VM_CHECK_INTERFACE;
    cxt.show_progress = options->show_progress && cxt.run_solver;
    struct DeclGroup *group = module->interface;
    while (group) {
        verify_decl_group(&cxt, group->decl);
        group = group->next;
    }

    if (options->mode == VM_LOAD_INTERFACE_CHECK_IMPL) {
        cxt.run_solver = true;
        cxt.show_progress = options->show_progress;

        // Verify each decl in the implementation.
        group = module->implementation;
        while (group) {
            verify_decl_group(&cxt, group->decl);
            group = group->next;
        }
    }

    free_hash_table(cxt.local_counter);
    free_hash_table(cxt.refs);
    free_hash_table(cxt.local_to_version);
    free_hash_table(cxt.local_hidden);

    if (cxt.debug_filename_prefix) {
        hash_table_for_each(cxt.debug_files_created, ht_free_key, NULL);
        free_hash_table(cxt.debug_files_created);
    }

    return !cxt.error_found;
}
