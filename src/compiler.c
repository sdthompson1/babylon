/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "alloc.h"
#include "ast.h"
#include "cache_db.h"
#include "compiler.h"
#include "debug_print.h"
#include "error.h"
#include "hash_table.h"
#include "initial_env.h"
#include "location.h"
#include "util.h"

// compiler stages
#include "lexer.h"
#include "parser.h"
#include "renamer.h"
#include "dependency.h"
#include "typechecker.h"
#include "verifier.h"
#include "codegen.h"

#include <stdlib.h>
#include <string.h>

struct StringNode {
    const char *ptr;
    struct StringNode *next;
};

static void add_string(struct StringNode **node, const char *ptr)
{
    struct StringNode *new_node = alloc(sizeof(struct StringNode));
    new_node->ptr = ptr;
    new_node->next = *node;
    *node = new_node;
}


struct LoadDetails {
    // key = module name (allocated)
    // value = NULL if module loading still in progress, or the module's
    // interface-fingerprint (32 bytes, allocated on heap) if the module
    // is fully loaded.
    struct HashTable *loaded_modules;

    struct HashTable *renamer_env;
    struct HashTable *type_env;
    struct VerifierEnv *verifier_env;
    struct HashTable *codegen_env;
    struct StringNode *strings;

    const char *module_name;
    const char *input_prefix;
    const char *output_prefix;
    struct Location import_location;  // location of import stmt if any

    enum CompileMode compile_mode;
    bool root_module;

    bool show_progress;
    bool create_debug_files;
    bool continue_after_verify_error;
    int verify_timeout_seconds;
    bool generate_main;
    bool auto_main;

    struct CacheDb *cache_db;
};

static void interpret_filename(struct LoadDetails *details, const char *filename)
{
    const char *slash = strrchr(filename, '/');
    if (slash == NULL) {
        details->input_prefix = copy_string("");
    } else {
        // +2 for the '/' character and null terminator
        char *prefix = alloc(slash - filename + 2);
        memcpy(prefix, filename, slash - filename + 1);
        prefix[slash - filename + 1] = 0;
        details->input_prefix = prefix;
        filename = slash + 1;
    }
    add_string(&details->strings, details->input_prefix);

    char *modname = NULL;
    const char *dot = strrchr(filename, '.');
    if (dot != NULL) {
        if (strcmp(dot, ".b") == 0 && dot != filename) {
            modname = alloc(dot - filename + 1);  // +1 for null terminator
            memcpy(modname, filename, dot - filename);
            modname[dot - filename] = 0;
        }
    }

    if (modname == NULL) {
        // Assume entire filename (after the last slash) is the module name
        modname = copy_string(filename);
    }

    details->module_name = modname;
    add_string(&details->strings, modname);
}

// *filename result is malloc'd.
static FILE * open_module_file(const struct LoadDetails *details,
                               const char **filename)
{
    *filename = copy_string_3(details->input_prefix, details->module_name, ".b");
    return fopen(*filename, "rb");
}


static char * get_output_filename(const struct LoadDetails *details,
                                  const char *suffix)
{
    return copy_string_3(details->output_prefix, details->module_name, suffix);
}

static bool load_module_recursive(struct LoadDetails *details);

bool load_imports(struct LoadDetails *details, struct Module *module, struct Import *imports)
{
    for (struct Import *import = imports; import; import = import->next) {

        const char *old_module_name = details->module_name;
        struct Location old_import_location = details->import_location;
        bool old_root_module = details->root_module;

        details->module_name = import->module_name;
        details->import_location = import->location;
        details->root_module = false;

        bool load_success = load_module_recursive(details);

        details->module_name = old_module_name;
        details->import_location = old_import_location;
        details->root_module = old_root_module;

        if (!load_success) {
            return false;
        }
    }

    return true;
}

static void add_import_hashes(struct SHA256_CTX *ctx, struct Import *imports, struct HashTable *loaded_modules)
{
    for (struct Import *import = imports; import; import = import->next) {
        const uint8_t *other_hash = hash_table_lookup(loaded_modules, import->module_name);
        if (other_hash == NULL) {
            fatal_error("module lookup failed");
        }
        sha256_add_bytes(ctx, (uint8_t*)"D#", 3);
        sha256_add_bytes(ctx, other_hash, SHA256_HASH_LENGTH);
    }
}

// Returns true if success, false if error (e.g. module not found, circular dependency)
static bool load_module_from_disk(struct LoadDetails *details)
{
    // Lex
    const struct Token *token = NULL;
    bool found = false;

    bool interface_only;
    if (details->root_module) {
        // Always load the root module in full.
        interface_only = false;
    } else if (details->compile_mode == CM_COMPILE || details->compile_mode == CM_VERIFY_ALL) {
        // In these modes we need to fully load all modules (not just the root).
        interface_only = false;
    } else {
        // Otherwise, we don't need to fully load this module - we only need its interface.
        interface_only = true;
    }

    // Load from filesystem
    const char *filename;
    FILE *file = open_module_file(details, &filename);
    add_string(&details->strings, filename);
    if (file) {
        found = true;
        token = lex(filename, file, interface_only);
        fclose(file);
    }

    if (token == NULL) {
        if (!found) {
            report_module_not_found(details->import_location, details->module_name, filename);
        }
        return false;
    }

    // Parse
    struct Module *module = parse_module(token, interface_only);
    if (module == NULL) {
        free_token((void*)token);
        return false;
    }

    if (strcmp(module->name, details->module_name) != 0) {
        struct Location loc = token->location;
        loc.begin_line_num = loc.end_line_num = 0;
        report_module_name_mismatch_filename(loc, module->name);
        free_module(module);
        free_token((void*)token);
        return false;
    }

    free_token((void*)token);

    // Ensure all imports are loaded
    if (!load_imports(details, module, module->interface_imports)
    || !load_imports(details, module, module->implementation_imports)) {
        free_module(module);
        return false;
    }

    // Create a "fingerprint" of this module's interface.
    // The fingerprint of a module's interface is the SHA256 hash of the
    // following:
    //  (a) the SHA256 hash of the interface tokens (as created by parser.c)
    //  (b) the fingerprints of any modules imported by the interface.
    // (mixed with some arbitrary made-up strings like "IN#" or "D#" just
    // to make it a bit more unique).
    struct SHA256_CTX ctx;
    sha256_init(&ctx);
    sha256_add_bytes(&ctx, (const uint8_t*)"IN#", 4);
    sha256_add_bytes(&ctx, module->interface_checksum, SHA256_HASH_LENGTH);
    add_import_hashes(&ctx, module->interface_imports, details->loaded_modules);

    // The interface fingerprint is stored in the loaded_modules hash table.
    uint8_t *interface_fingerprint = alloc(SHA256_HASH_LENGTH);
    struct SHA256_CTX ctx2 = ctx;
    sha256_final(&ctx2, interface_fingerprint);
    hash_table_insert(details->loaded_modules, module->name, interface_fingerprint);

    // We now create a fingerprint of the full module.
    // This is the SHA256 of (a) and (b) above, together with:
    //  (c) the SHA256 of the implementation tokens
    //  (d) the fingerprints of any modules imported by the implementation.
    uint8_t full_module_fingerprint[SHA256_HASH_LENGTH] = {0};
    sha256_add_bytes(&ctx, (const uint8_t*)"IM#", 4);
    sha256_add_bytes(&ctx, module->implementation_checksum, SHA256_HASH_LENGTH);
    add_import_hashes(&ctx, module->implementation_imports, details->loaded_modules);
    sha256_final(&ctx, full_module_fingerprint);

    // Rename (in place)
    if (!rename_module(details->renamer_env, module, interface_only)) {
        free_module(module);
        return false;
    }

    // Resolve dependencies (in place)
    resolve_dependencies(module);

    // Typecheck
    bool keep_all_types = false;
    if (!typecheck_module(details->type_env, module, interface_only, keep_all_types)) {
        free_module(module);
        return false;
    }

    // Print module post-typechecking (if requested)
    if (details->create_debug_files) {
        char *debug_filename = get_output_filename(details, ".tychk");
        FILE *debug_file = fopen(debug_filename, "w");
        free(debug_filename);
        if (debug_file) {
            print_module(debug_file, module);
            fclose(debug_file);
        }
    }

    // Verify (if requested)
    if (details->compile_mode == CM_VERIFY || details->compile_mode == CM_VERIFY_ALL) {
        if (!interface_only) {
            // See if we can find this module's fingerprint in the cache.
            // If so, that means we have in the past verified a module with
            // identical text, and identical imported interfaces. Therefore
            // there is no need to verify it again.
            if (sha256_exists_in_db(details->cache_db, full_module_fingerprint)) {
                if (details->show_progress) {
                    fprintf(stderr, "Skipping module %s (cached)\n", module->name);
                }

                // No need to run a full verification.
                // We do still need to run in interface_only mode, so that
                // any required decls are added to the verification context
                // (i.e. in case they are imported by future modules).
                interface_only = true;
            }
        }

        struct VerifierOptions options;
        options.cache_db = details->cache_db;
        options.debug_filename_prefix = NULL;
        if (details->create_debug_files) {
            options.debug_filename_prefix = get_output_filename(details, "");
        }
        options.timeout_seconds = details->verify_timeout_seconds;
        options.interface_only = interface_only;
        options.show_progress = !interface_only && details->show_progress;
        options.continue_after_error = details->continue_after_verify_error;
        bool result = verify_module(details->verifier_env,
                                    module,
                                    &options);
        free((char*)options.debug_filename_prefix);
        if (!result) {
            free_module(module);
            return false;
        }

        // Successful verification. Store the module's fingerprint in
        // the cache (if this was a full verification), so that we know
        // not to verify it again in future.
        if (!interface_only && details->cache_db) {
            add_sha256_to_db(details->cache_db, full_module_fingerprint);
        }
    }

    // Check existence of main (if this is the root)
    if (details->root_module) {
        if (details->auto_main) {
            char *main_name = copy_string_2(module->name, ".main");
            details->generate_main = hash_table_contains_key(details->type_env, main_name);
            free(main_name);
        }
        if (details->generate_main && !typecheck_main_function(details->type_env, module->name)) {
            free_module(module);
            return false;
        }
    }

    // Compile (if requested)
    if (details->compile_mode == CM_COMPILE) {
        char *c_filename = get_output_filename(details, ".c");
        char *h_filename = get_output_filename(details, ".h");
        FILE *c_file = fopen(c_filename, "w");
        FILE *h_file = fopen(h_filename, "w");
        if (!c_file || !h_file) {
            if (c_file) {
                fclose(c_file);
            } else {
                report_failed_to_open_c_file(c_filename);
            }
            if (h_file) {
                fclose(h_file);
            } else {
                report_failed_to_open_c_file(h_filename);
            }
            free(c_filename);
            free(h_filename);
            free_module(module);
            return false;
        }
        free(c_filename);
        free(h_filename);
        codegen_module(c_file, h_file, details->codegen_env, module, details->root_module, details->generate_main);
        fclose(c_file);
        fclose(h_file);
    }

    free_module(module);
    return true;
}

// Returns true if success, false if error (e.g. module not found, circular dependency)
static bool load_module_recursive(struct LoadDetails *details)
{
    const char *key_out = NULL;
    void *value_out = NULL;
    hash_table_lookup_2(details->loaded_modules, details->module_name, &key_out, &value_out);

    if (value_out != NULL) {
        // Module was previously loaded. Nothing to do.
        return true;
    }

    if (key_out != NULL) {
        // Circular dependency.
        report_circular_dependency(details->import_location, details->module_name);
        return false;
    }

    // The module is now loading
    hash_table_insert(details->loaded_modules, copy_string(details->module_name), NULL);

    // Load the module, either as a built-in module, or from disk.
    if (import_builtin_module(details->module_name,
                              details->renamer_env,
                              details->type_env,
                              details->verifier_env,
                              details->codegen_env)) {
        // HACK: just use a "fake" SHA256 hash for now.
        // TODO: We probably should remove builtin modules sometime.
        char *hash = alloc(SHA256_HASH_LENGTH);
        for (int i = 0; i < SHA256_HASH_LENGTH; ++i) {
            hash[i] = i;
        }
        hash_table_insert(details->loaded_modules, details->module_name, hash);
    } else {
        if (!load_module_from_disk(details)) {
            return false;
        }
    }

    return true;
}

bool compile(struct CompileOptions *options)
{
    struct LoadDetails details;

    details.loaded_modules = new_hash_table();
    details.renamer_env = new_hash_table();
    details.type_env = new_hash_table();
    details.verifier_env = new_verifier_env();
    details.codegen_env = new_codegen_env();
    details.strings = NULL;

    interpret_filename(&details, options->filename);
    if (options->output_prefix) {
        details.output_prefix = options->output_prefix;
    } else {
        details.output_prefix = details.input_prefix;
    }

    if (options->cache_mode == CACHE_DISABLED) {
        details.cache_db = NULL;
    } else {
        details.cache_db = open_cache_db(details.output_prefix);
    }

    details.import_location = g_no_location;
    details.compile_mode = options->mode;
    details.root_module = true;

    details.show_progress = options->show_progress;
    details.create_debug_files = options->create_debug_files;
    details.continue_after_verify_error = options->continue_after_verify_error;
    details.verify_timeout_seconds = options->verify_timeout_seconds;
    details.generate_main = options->generate_main;
    details.auto_main = options->auto_main;

    bool success = load_module_recursive(&details);

    close_cache_db(details.cache_db);
    details.cache_db = NULL;

    free_verifier_env(details.verifier_env);

    hash_table_for_each(details.loaded_modules, ht_free_key_and_value, NULL);
    free_hash_table(details.loaded_modules);

    free_renamer_env(details.renamer_env);
    free_type_env(details.type_env);
    free_codegen_env(details.codegen_env);

    struct StringNode *strings = details.strings;
    while (strings) {
        free((char*)strings->ptr);
        struct StringNode *to_free = strings;
        strings = strings->next;
        free(to_free);
    }

    return success;
}
