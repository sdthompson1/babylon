/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "hash_table.h"
#include "initial_env.h"
#include "util.h"
#include "verifier.h"
#include "verifier_context.h"
#include "verifier_decls.h"

#include <stdlib.h>

struct VerifierEnv * new_verifier_env()
{
    struct VerifierEnv *env = alloc(sizeof(struct VerifierEnv));
    env->table = new_hash_table();
    setup_initial_verifier_env(env);
    return env;
}

void free_verifier_env(struct VerifierEnv *env)
{
    clear_verifier_env_hash_table(env->table);
    free_hash_table(env->table);
    free(env);
}

static void backup_name(struct HashTable *backup, struct HashTable *env, const char *decl_name)
{
    const char *fol_name = copy_string_2("%", decl_name);
    struct Item *item = copy_item(hash_table_lookup(env, fol_name));
    hash_table_insert(backup, fol_name, item);
}

static struct HashTable * backup_impl_decls(struct HashTable *env,
                                            struct Module *module)
{
    struct HashTable *backup_table = new_hash_table();

    for (struct DeclGroup *group = module->implementation; group; group = group->next) {
        for (struct Decl *decl = group->decl; decl; decl = decl->next) {
            backup_name(backup_table, env, decl->name);
        }
    }

    return backup_table;
}

static void restore_impl_decls(struct HashTable *env, struct HashTable *backup_table)
{
    struct HashIterator *iter = new_hash_iterator(backup_table);
    const char *backup_name;
    void *backup_item;
    while (hash_iterator_next(iter, &backup_name, &backup_item)) {
        remove_existing_item(env, backup_name);
        if (backup_item != NULL) {
            hash_table_insert(env, backup_name, backup_item);
        } else {
            free((void*)backup_name);
        }
    }
    free_hash_iterator(iter);
    free_hash_table(backup_table);
}

bool verify_module(struct VerifierEnv *verifier_env,
                   struct Module *module,
                   struct VerifierOptions *options)
{
    struct VContext cxt;
    cxt.global_env = verifier_env->table;
    cxt.local_env = new_hash_table();
    cxt.local_to_version = new_hash_table();
    cxt.local_counter = new_hash_table();
    cxt.string_names = new_hash_table();
    cxt.refs = new_hash_table();
    cxt.var_decl_stack = NULL;
    cxt.new_values = NULL;
    cxt.path_condition = NULL;
    cxt.facts = NULL;
    cxt.num_facts = 0;
    cxt.interface_only = options->interface_only;
    cxt.function_args = NULL;
    cxt.arglist_sexpr = cxt.funapp_sexpr = NULL;
    cxt.postconds = NULL;
    cxt.assert_exprs = NULL;
    cxt.show_progress = options->show_progress;
    cxt.timeout_seconds = options->timeout_seconds;
    cxt.continue_after_error = options->continue_after_error;
    cxt.error_found = false;

    cxt.debug_filename_prefix = options->debug_filename_prefix;
    if (cxt.debug_filename_prefix) {
        cxt.debug_files_created = new_hash_table();
    } else {
        cxt.debug_files_created = NULL;
    }
    cxt.cache_prefix = options->cache_prefix;


    bool ok = true;

    // Verify each decl in the interface
    struct DeclGroup *group = module->interface;
    while (group) {
        ok = verify_decl_group(&cxt, group->decl) && ok;
        group = group->next;
    }

    if (!cxt.interface_only) {
        // Take backup copies of all implementation decls
        struct HashTable * backup = backup_impl_decls(verifier_env->table, module);

        // Verify each decl in the implementation.
        group = module->implementation;
        while (group) {
            ok = verify_decl_group(&cxt, group->decl) && ok;
            group = group->next;
        }

        // Revert back to the backups, as we don't want to keep implementation
        // things in the environment after the module is processed.
        restore_impl_decls(verifier_env->table, backup);
    }

    hash_table_for_each(cxt.string_names, ht_free_key, NULL);
    free_hash_table(cxt.string_names);

    free_hash_table(cxt.local_counter);
    free_hash_table(cxt.refs);
    free_hash_table(cxt.local_to_version);
    free_hash_table(cxt.local_env);

    if (cxt.debug_filename_prefix) {
        hash_table_for_each(cxt.debug_files_created, ht_free_key, NULL);
        free_hash_table(cxt.debug_files_created);
    }

    if (ok != (!cxt.error_found)) {
        fatal_error("inconsistency between 'ok' and 'error_found' flags");
    }

    return ok;
}
