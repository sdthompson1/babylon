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
#include "fol.h"
#include "hash_table.h"
#include "initial_env.h"
#include "location.h"
#include "stacked_hash_table.h"
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

#include <errno.h>
#include <sys/stat.h>
#include <sys/types.h>

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
    TypeEnv *type_env;
    TypeEnv *expanded_type_env;  // used for codegen. contains 'expanded' versions of abstract types.
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
    char *name = replace_dots_with_slashes(details->module_name);
    *filename = copy_string_3(details->input_prefix, name, ".b");
    free(name);
    return fopen(*filename, "rb");
}


// Returns true on success.
static bool maybe_mkdir(const char *path, mode_t mode)
{
    errno = 0;

    // Try to make the directory.
    if (mkdir(path, mode) == 0) {
        // Success.
        return true;
    }

    if (errno != EEXIST) {
        // Failed for some reason other than EEXIST.
        return false;
    }

    struct stat st;
    if (stat(path, &st) != 0) {
        // Failed to stat the existing thing.
        return false;
    }

    if (!S_ISDIR(st.st_mode)) {
        // There is an existing thing (not a directory) blocking the directory creation.
        return false;
    }

    // The directory already exists so we are OK.
    return true;
}

static void make_parent_dirs(char *path, size_t prefix_len)
{
    const mode_t mode = 0777;
    for (char *p = path + prefix_len; *p; ++p) {
        if (*p == '/') {
            *p = 0;
            if (!maybe_mkdir(path, mode)) {
                report_mkdir_failed(path);
                *p = '/';
                break;
            }
            *p = '/';
        }
    }
}

static char * get_output_filename(const struct LoadDetails *details,
                                  const char *suffix)
{
    char *name = replace_dots_with_slashes(details->module_name);
    char *result = copy_string_3(details->output_prefix, name, suffix);
    free(name);
    make_parent_dirs(result, strlen(details->output_prefix));
    return result;
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

static void add_import_fingerprints(struct SHA256_CTX *ctx, struct Import *imports, struct HashTable *loaded_modules)
{
    for (struct Import *import = imports; import; import = import->next) {
        const uint8_t *other_hash = hash_table_lookup(loaded_modules, import->module_name);
        if (other_hash == NULL) {
            fatal_error("module lookup failed");
        }
        const char *imp_fpr = "IMP-FPR";  // "import fingerprint"
        sha256_add_bytes(ctx, (uint8_t*)imp_fpr, strlen(imp_fpr)+1);
        sha256_add_bytes(ctx, other_hash, SHA256_HASH_LENGTH);
    }
}

static bool run_typechecker(struct LoadDetails *details,
                            TypeEnv *env,
                            struct Module *module,
                            bool interface_only)
{
    if (!typecheck_module(env, module, interface_only)) {
        return false;
    }

    // Print module post-typechecking (if requested)
    if (details->create_debug_files) {
        char *debug_filename = get_output_filename(details, interface_only ? ".tychk_int" : ".tychk_impl");
        FILE *debug_file = fopen(debug_filename, "w");
        free(debug_filename);
        if (debug_file) {
            print_module(debug_file, module, interface_only);
            fclose(debug_file);
        }
    }

    return true;
}

static bool should_skip_module(struct LoadDetails *details,
                               struct Module *module,
                               const uint8_t full_module_fingerprint[SHA256_HASH_LENGTH])
{
    // See if we can find this module's fingerprint in the cache.
    // If so, that means we have in the past verified a module with
    // identical text, and identical imported interfaces. Therefore
    // there is no need to verify it again.
    if (sha256_exists_in_db(details->cache_db, MODULE_HASH, full_module_fingerprint)) {
        if (details->show_progress) {
                add_fol_message(copy_string_3("Skipping module ", module->name, " (cached)\n"),
                                false,  // is_error
                                0, NULL);
        }
        return true;
    } else {
        return false;
    }
}

static bool run_verifier(struct LoadDetails *details,
                         struct Module *module,
                         enum VerifierMode mode,
                         const uint8_t full_module_fingerprint[SHA256_HASH_LENGTH])
{
    struct VerifierOptions options;
    options.cache_db = details->cache_db;
    options.debug_filename_prefix = NULL;
    if (details->create_debug_files) {
        options.debug_filename_prefix = get_output_filename(details, "");
    }
    options.mode = mode;
    options.show_progress = details->show_progress;
    bool result = verify_module(details->verifier_env,
                                module,
                                &options);
    free((char*)options.debug_filename_prefix);
    if (!result) {
        return false;
    }

    // If this was a full verification (VM_LOAD_INTERFACE_CHECK_IMPL),
    // then schedule the module's fingerprint to be stored into the
    // cache, so that we know not to verify the same module again in
    // the future.
    if (mode == VM_LOAD_INTERFACE_CHECK_IMPL) {
        add_fol_message(NULL, false, MODULE_HASH, full_module_fingerprint);
    }

    return true;
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
    // (mixed with some arbitrary made-up strings like "INT-CHKSUM" just
    // to make it a bit more unique).
    struct SHA256_CTX ctx;
    sha256_init(&ctx);
    const char *int_chksum = "INT-CHKSUM";
    sha256_add_bytes(&ctx, (const uint8_t*)int_chksum, strlen(int_chksum)+1);
    sha256_add_bytes(&ctx, module->interface_checksum, SHA256_HASH_LENGTH);
    add_import_fingerprints(&ctx, module->interface_imports, details->loaded_modules);

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
    const char *impl_chksum = "IMPL-CHKSUM";
    sha256_add_bytes(&ctx, (const uint8_t*)impl_chksum, strlen(impl_chksum)+1);
    sha256_add_bytes(&ctx, module->implementation_checksum, SHA256_HASH_LENGTH);
    add_import_fingerprints(&ctx, module->implementation_imports, details->loaded_modules);
    sha256_final(&ctx, full_module_fingerprint);

    // Rename (in place)
    if (!rename_module(details->renamer_env, module, interface_only)) {
        free_module(module);
        return false;
    }

    // Resolve dependencies (in place)
    resolve_dependencies(module);

    // We can skip verification if we are in CM_VERIFY (not CM_VERIFY_ALL) mode,
    // and this is not the root module.
    bool skip = (details->compile_mode == CM_VERIFY && !details->root_module);

    // We can also skip verification if the module's fingerprint is in the cache
    // (as this means the exact same module was verified on a previous run).
    skip = skip ||
        ((details->compile_mode == CM_VERIFY || details->compile_mode == CM_VERIFY_ALL)
         && should_skip_module(details, module, full_module_fingerprint));

    if (skip) {
        // We can skip verification but we still need to typecheck, and
        // load the module's interface into the verifier.

        // Typecheck interface, keeping the results in type env.
        details->type_env = push_type_env(details->type_env);
        if (!run_typechecker(details, details->type_env, module, true)) {
            free_module(module);
            return false;
        }
        details->type_env = collapse_type_env(details->type_env);

        // Verify the interface, keeping the results in verifier env.
        push_verifier_env(details->verifier_env);
        if (!run_verifier(details, module, VM_LOAD_INTERFACE, full_module_fingerprint)) {
            free_module(module);
            return false;
        }
        collapse_verifier_env(details->verifier_env);

    } else if (details->compile_mode == CM_VERIFY || details->compile_mode == CM_VERIFY_ALL) {
        // We need to do a full verification of the module.

        // We do this in several steps, in order to be able to handle
        // abstract types ("type Foo;" in the interface).

        // First, typecheck and verify the interface, leaving new
        // layers on top of the type and verifier envs for now. Do
        // this on a separate copy of the module.

        struct Module *copy = copy_module(module);

        details->type_env = push_type_env(details->type_env);
        if (!run_typechecker(details, details->type_env, copy, true)) {
            free_module(copy);
            free_module(module);
            return false;
        }

        push_verifier_env(details->verifier_env);
        if (!run_verifier(details, copy, VM_CHECK_INTERFACE, full_module_fingerprint)) {
            free_module(copy);
            free_module(module);
            return false;
        }

        free_module(copy);

        // Now typecheck and verify the whole module, using
        // "temporary" type and verifier envs (which will be
        // discarded).

        TypeEnv * temp_type_env = push_type_env(details->type_env->base);
        if (!run_typechecker(details, temp_type_env, module, false)) {
            pop_type_env(temp_type_env);
            free_module(module);
            return false;
        }
        pop_type_env(temp_type_env);
        temp_type_env = NULL;

        struct HashTable *backup = detach_verifier_env_layer(details->verifier_env);
        push_verifier_env(details->verifier_env);
        bool verify_result = run_verifier(details, module, VM_LOAD_INTERFACE_CHECK_IMPL, full_module_fingerprint);
        pop_verifier_env(details->verifier_env);
        attach_verifier_env_layer(details->verifier_env, backup);
        if (!verify_result) {
            free_module(module);
            return false;
        }

        // We can now keep the results from the INTERFACE typecheck
        // and verification.
        details->type_env = collapse_type_env(details->type_env);
        collapse_verifier_env(details->verifier_env);

    } else if (details->compile_mode == CM_COMPILE) {
        // First typecheck the interface (using the "abstracted"
        // types) - on a copy of the module.
        struct Module *copy = copy_module(module);
        details->type_env = push_type_env(details->type_env);
        if (!run_typechecker(details, details->type_env, copy, true)) {
            free_module(copy);
            free_module(module);
            return false;
        }
        free_module(copy);
        copy = NULL;
        details->type_env = collapse_type_env(details->type_env);

        // Now typecheck the whole module (using the "expanded" types)
        // - on the original module.
        details->expanded_type_env = push_type_env(details->expanded_type_env);
        if (!run_typechecker(details, details->expanded_type_env, module, false)) {
            free_module(module);
            return false;
        }
        details->expanded_type_env = collapse_type_env(details->expanded_type_env);
    }

    // Check existence of main (if this is the root)
    if (details->root_module) {
        if (details->auto_main) {
            char *main_name = copy_string_2(module->name, ".main");
            details->generate_main = (type_env_lookup(details->type_env, main_name) != NULL);
            free(main_name);
        }
        // Complete verification jobs before attempting to typecheck main
        // (as we don't want the error messages "mixed")
        wait_fol_complete();
        if (!fol_error_found()
        && details->generate_main
        && !typecheck_main_function(details->type_env, module->name)) {
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
    update_fol_status();
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
                              details->expanded_type_env,
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
    details.type_env = new_type_env();
    details.expanded_type_env = new_type_env();
    details.verifier_env = new_verifier_env();
    details.codegen_env = new_codegen_env();
    details.strings = NULL;

    interpret_filename(&details, options->filename);
    if (options->output_prefix) {
        details.output_prefix = options->output_prefix;
    } else {
        details.output_prefix = details.input_prefix;
    }

    // Open the cache unless (a) it is disabled or (b) we are only compiling,
    // not verifying (in which case the cache is not needed).
    if (options->cache_mode == CACHE_DISABLED || options->mode == CM_COMPILE) {
        details.cache_db = NULL;
    } else {
        details.cache_db = open_cache_db(details.output_prefix);
    }

    start_fol_runner(details.cache_db,
                     options->verify_timeout_seconds,
                     options->continue_after_verify_error);

    details.import_location = g_no_location;
    details.compile_mode = options->mode;
    details.root_module = true;

    details.show_progress = options->show_progress;
    details.create_debug_files = options->create_debug_files;
    details.generate_main = options->generate_main;
    details.auto_main = options->auto_main;

    bool success = load_module_recursive(&details);

    // Wait for FOL runner to complete, and then get final status
    wait_fol_complete();
    success = success && !fol_error_found();
    stop_fol_runner();

    // Close cache DB (*after* FOL runner has finished!)
    close_cache_db(details.cache_db);
    details.cache_db = NULL;

    free_verifier_env(details.verifier_env);

    hash_table_for_each(details.loaded_modules, ht_free_key_and_value, NULL);
    free_hash_table(details.loaded_modules);

    free_renamer_env(details.renamer_env);
    free_type_env(details.type_env);
    free_type_env(details.expanded_type_env);
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
