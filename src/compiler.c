/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
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


static const char LOADING;
static const char LOADED;


struct LoadDetails {
    struct HashTable *loaded_modules;   // keys are allocated. values are &LOADING or &LOADED.
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
        struct VerifierOptions options;
        options.cache_prefix = copy_string_2(details->output_prefix, "cache/");
        options.debug_filename_prefix = NULL;
        if (details->create_debug_files) {
            options.debug_filename_prefix = get_output_filename(details, "");
        }
        options.timeout_seconds = details->verify_timeout_seconds;
        options.interface_only =
            details->compile_mode == CM_VERIFY && !details->root_module;
        options.show_progress = details->show_progress;
        options.continue_after_error = details->continue_after_verify_error;
        bool result = verify_module(details->verifier_env,
                                    module,
                                    &options);
        free((char*)options.debug_filename_prefix);
        free((char*)options.cache_prefix);
        if (!result) {
            free_module(module);
            return false;
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
        char *asm_filename = get_output_filename(details, ".s");
        FILE *asm_file = fopen(asm_filename, "w");
        if (!asm_file) {
            report_failed_to_open_asm_file(asm_filename);
            free(asm_filename);
            free_module(module);
            return false;
        }
        free(asm_filename);
        codegen_module(asm_file, details->codegen_env, module, details->root_module, details->generate_main);
        fclose(asm_file);
    }

    free_module(module);
    return true;
}

// Returns true if success, false if error (e.g. module not found, circular dependency)
static bool load_module_recursive(struct LoadDetails *details)
{
    void *module_lookup = hash_table_lookup(details->loaded_modules, details->module_name);

    if (module_lookup == &LOADED) {
        // Nothing to do
        return true;
    }

    if (module_lookup == &LOADING) {
        // Circular dependency
        report_circular_dependency(details->import_location, details->module_name);
        return false;
    }

    // The module is now loading
    hash_table_insert(details->loaded_modules, copy_string(details->module_name), (void*)&LOADING);

    // Load the module, either as a built-in module, or from disk.
    if (!import_builtin_module(details->module_name,
                               details->renamer_env,
                               details->type_env,
                               details->verifier_env,
                               details->codegen_env)) {
        if (!load_module_from_disk(details)) {
            return false;
        }
    }

    // The module is now fully loaded
    hash_table_insert(details->loaded_modules, details->module_name, (void*)&LOADED);

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

    free_verifier_env(details.verifier_env);

    hash_table_for_each(details.loaded_modules, ht_free_key, NULL);
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
