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
#include "config_file.h"
#include "debug_print.h"
#include "error.h"
#include "fol.h"
#include "hash_table.h"
#include "initial_env.h"
#include "location.h"
#include "make_dir.h"
#include "package.h"
#include "process.h"
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

#include <ctype.h>
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
    // key = module name ("package-name/ModuleName"; allocated)
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

    const char *root_package_name;

    const char *importer_package_name;
    const char *module_name;
    struct PackageLoader *package_loader;
    const char *output_prefix;
    struct Location import_location;  // location of import stmt if any

    enum CompileMode compile_mode;
    struct NameList *requested_modules;
    const char *main_module_name;
    const char *main_function_name;

    bool show_progress;
    bool create_debug_files;

    struct CacheDb *cache_db;

    struct NameList *obj_files;  // object files to link

    // Compile settings
    const char *cc_cmd;
    const char *ld_cmd;
    struct NameList *cflags;
    struct NameList *libs;
    bool run_c_compiler;
    bool print_c_compiler_commands;
};


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
                                  const struct Module *module,
                                  const char *prefix,
                                  const char *suffix)
{
    char *name = replace_dots_with_slashes(module->name);
    char *result = copy_string_4(details->output_prefix, prefix, name, suffix);
    free(name);
    make_parent_dirs(result, strlen(details->output_prefix));
    return result;
}


static bool load_module_recursive(struct LoadDetails *details);

bool load_imports(struct LoadDetails *details,
                  const char *importer_package_name,
                  struct Module *module,
                  struct Import *imports)
{
    for (struct Import *import = imports; import; import = import->next) {

        const char *old_package_name = details->importer_package_name;
        const char *old_module_name = details->module_name;
        struct Location old_import_location = details->import_location;

        details->importer_package_name = importer_package_name;
        details->module_name = import->module_name;
        details->import_location = import->location;

        bool load_success = load_module_recursive(details);

        details->importer_package_name = old_package_name;
        details->module_name = old_module_name;
        details->import_location = old_import_location;

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
        char *debug_filename = get_output_filename(details,
                                                   module,
                                                   "debug_typecheck/",
                                                   interface_only ? ".tychk_int" : ".tychk_impl");
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
            char *new_name = sanitise_name(module->name);
            add_fol_message(copy_string_3("Skipping module ", new_name, " (cached)\n"),
                            false,  // is_error
                            0, NULL);
            free(new_name);
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
        options.debug_filename_prefix = get_output_filename(details, module, "debug_verify/", "");
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

static bool needs_quote(const char *str)
{
    while (*str) {
        char c = *str;
        // These are "known safe" characters:
        if (isalnum(c) || c == ',' || c == '.' || c == '_' || c == '+'
        || c == ':' || c == '@' || c == '%' || c == '/' || c == '-') {
            ++str;
        } else {
            // Unsafe character found - needs quoting
            return true;
        }
    }
    return false;
}

static void print_quoted(const char *p)
{
    bool in_quote = false;
    while (*p) {
        if (*p == '\'') {
            if (in_quote) {
                putchar('\'');
                in_quote = false;
            }
            printf("\\'");
        } else {
            if (!in_quote) {
                putchar('\'');
                in_quote = true;
            }
            putchar(*p);
        }
        ++p;
    }
    if (in_quote) {
        putchar('\'');
    }
}

static void print_cmd_array(const char **cmd)
{
    // Print 'cmd' quoting any arguments as necessary.
    // Note this assumes a Bash-like shell.
    bool first = true;
    while (*cmd) {
        if (!first) {
            printf(" ");
        }
        if (needs_quote(*cmd)) {
            print_quoted(*cmd);
        } else {
            printf("%s", *cmd);
        }
        ++cmd;
        first = false;
    }
    printf("\n");
}

static bool compile_c_file(struct LoadDetails *details,
                           const char *package_name,
                           const char *c_filename,
                           const char *o_filename)
{
    char *include_dir = copy_string_2(details->output_prefix, "c");

    struct NameList *pkg_cflags = get_package_cflags(details->package_loader, package_name);

    // $(CC) $(CFLAGS) -I include_dir -c filename.c -o filename.o

    int num_cflags = name_list_length(pkg_cflags) + name_list_length(details->cflags);

    const char **cmd = alloc(sizeof(char*) * (8 + num_cflags));
    cmd[0] = details->cc_cmd;
    int idx = 1;
    for (struct NameList *node = details->cflags; node; node = node->next) {
        cmd[idx++] = node->name;
    }
    for (struct NameList *node = pkg_cflags; node; node = node->next) {
        cmd[idx++] = node->name;
    }
    cmd[idx++] = "-I";
    cmd[idx++] = include_dir;
    cmd[idx++] = "-c";
    cmd[idx++] = c_filename;
    cmd[idx++] = "-o";
    cmd[idx++] = o_filename;
    cmd[idx++] = NULL;

    if (details->print_c_compiler_commands) {
        print_cmd_array(cmd);
    }

    struct Process proc;
    default_init_process(&proc);
    proc.cmd = cmd;
    proc.show_stdout = true;  // allow the compiler to print to stdout (although most compilers don't, it seems)
    proc.show_stderr = true;  // allow the compiler to print to stderr
    launch_process(&proc);

    free(cmd);
    free(include_dir);

    // Wait for the compile job to finish before continuing.
    // (TODO: Parallel compilation jobs might be a good thing to add sometime - see also
    // the parallel job system in fol.c - maybe that could be abstracted out and re-used here?)
    while (proc.status == PROC_RUNNING) {
        update_processes(true);
    }

    struct NameList *node = alloc(sizeof(struct NameList));
    node->name = copy_string(o_filename);
    node->next = details->obj_files;
    details->obj_files = node;

    // The compilation is considered to have succeeded if the child process ran
    // to completion AND its exit status was zero.
    return proc.status == PROC_SUCCESS && proc.exit_status == 0;
}

static bool run_linker(const struct LoadDetails *details)
{
    struct NameList *pkg_libs = get_package_libs(details->package_loader);

    char *exe_name = copy_string_3(details->output_prefix, "bin/", details->root_package_name);
    make_parent_dirs(exe_name, strlen(details->output_prefix));

    // $(LD) -o exe_name object-files-list $(LIBS)

    int num_objects = name_list_length(details->obj_files);
    int num_libs = name_list_length(pkg_libs) + name_list_length(details->libs);

    const char **cmd = alloc(sizeof(char*) * (4 + num_objects + num_libs));

    cmd[0] = details->ld_cmd;
    cmd[1] = "-o";
    cmd[2] = exe_name;
    int idx = 3;
    for (struct NameList *node = details->obj_files; node; node = node->next) {
        cmd[idx++] = node->name;
    }
    for (struct NameList *node = details->libs; node; node = node->next) {
        cmd[idx++] = node->name;
    }
    for (struct NameList *node = pkg_libs; node; node = node->next) {
        cmd[idx++] = node->name;
    }
    cmd[idx++] = NULL;

    if (details->print_c_compiler_commands) {
        print_cmd_array(cmd);
    }

    struct Process proc;
    default_init_process(&proc);
    proc.cmd = cmd;
    proc.show_stderr = true;
    launch_process(&proc);

    free(exe_name);
    free(cmd);

    while (proc.status == PROC_RUNNING) {
        update_processes(true);
    }

    return proc.status == PROC_SUCCESS && proc.exit_status == 0;
}


// Returns true if success, false if error (e.g. module not found, circular dependency)
static bool load_module_from_disk(struct LoadDetails *details,
                                  struct ModulePathInfo *info)
{
    // Lex
    const struct Token *token = NULL;
    bool found = false;

    // If this module was explicitly requested, or if "all" modules were implicitly requested
    // (because requested_modules list was empty), then process the whole module.
    // Otherwise process only the interface.
    bool explicitly_requested =
        info
        && strcmp(details->root_package_name, info->package_name) == 0
        && name_list_contains_string(details->requested_modules, details->module_name);
    bool process_whole_module =
        details->requested_modules == NULL
        || explicitly_requested;
    bool interface_only = !process_whole_module;

    // Load from filesystem
    FILE *file = info ? fopen(info->b_filename, "rb") : NULL;
    if (file) {
        found = true;
        token = lex(info->b_filename, file, interface_only);
        fclose(file);
    }

    if (token == NULL) {
        if (!found) {
            report_module_not_found(details->import_location,
                                    details->module_name,
                                    info ? info->b_filename : NULL);
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
    if (!load_imports(details, info->package_name, module, module->interface_imports)) {
        free_module(module);
        return false;
    }
    if (!interface_only) {
        if (!load_imports(details, info->package_name, module, module->implementation_imports)) {
            free_module(module);
            return false;
        }
    }

    // Rename (in place)
    if (!rename_module(details->renamer_env,
                       details->package_loader,
                       info->package_name,
                       module,
                       interface_only)) {
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
    // Note: module->name is already in the table (with value NULL), so we do NOT
    // call copy_string(module->name), instead we just pass module->name so that it
    // finds the existing key (and updates the value).
    uint8_t *interface_fingerprint = alloc(SHA256_HASH_LENGTH);
    struct SHA256_CTX ctx2 = ctx;
    sha256_final(&ctx2, interface_fingerprint);
    hash_table_insert(details->loaded_modules, module->name, interface_fingerprint);

    // We now create a fingerprint of the full module.
    // This is the SHA256 of (a) and (b) above, together with:
    //  (c) the SHA256 of the implementation tokens
    //  (d) the fingerprints of any modules imported by the implementation.
    uint8_t full_module_fingerprint[SHA256_HASH_LENGTH] = {0};
    if (!interface_only) {
        const char *impl_chksum = "IMPL-CHKSUM";
        sha256_add_bytes(&ctx, (const uint8_t*)impl_chksum, strlen(impl_chksum)+1);
        sha256_add_bytes(&ctx, module->implementation_checksum, SHA256_HASH_LENGTH);
        add_import_fingerprints(&ctx, module->implementation_imports, details->loaded_modules);
        sha256_final(&ctx, full_module_fingerprint);
    }

    // Resolve dependencies (in place)
    resolve_dependencies(module);

    // We skip verification in interface_only mode.
    bool skip = (details->compile_mode == CM_VERIFY && interface_only);

    // We can also skip verification if the module's fingerprint is in the cache
    // (as this means the exact same module was verified on a previous run).
    skip = skip ||
        (details->compile_mode == CM_VERIFY
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

    } else if (details->compile_mode == CM_VERIFY) {
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

    // If main_module and main_function are both set, and this is the main_module,
    // then check that the main_function exists and has the expected type.
    const bool main_function_required =
        details->main_module_name
        && details->main_function_name
        && strcmp(info->package_name, details->root_package_name) == 0
        && strcmp(details->module_name, details->main_module_name) == 0;
    if (main_function_required) {
        // Complete verification jobs before attempting to typecheck main
        // (as we don't want the error messages "mixed")
        wait_fol_complete();
        if (!fol_error_found()
        && !typecheck_main_function(details->type_env, module->name, details->main_function_name)) {
            free_module(module);
            return false;
        }
    }

    // Compile (if requested)
    if (details->compile_mode == CM_COMPILE) {
        // Generate C code
        char *c_filename = get_output_filename(details, module, "c/", ".b.c");
        char *h_filename = get_output_filename(details, module, "c/", ".b.h");
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
        free(h_filename);
        codegen_module(c_file, h_file, details->codegen_env, module);

        if (main_function_required) {
            codegen_main_function(c_file, module, details->main_function_name);
        }

        fclose(c_file);
        fclose(h_file);

        // Now compile the C to an object file
        if (details->run_c_compiler) {
            char *o_filename = get_output_filename(details, module, "obj/", ".b.o");
            bool ok = compile_c_file(details, info->package_name, c_filename, o_filename);
            free(o_filename);
            if (!ok) {
                fprintf(stderr, "Compilation of %s failed\n", c_filename);
            }
            free(c_filename);
            if (!ok) {
                free_module(module);
                return false;
            }

            // If there is a user-supplied C file then compile that as well
            if (info->c_filename) {
                o_filename = get_output_filename(details, module, "obj/", ".o");
                ok = compile_c_file(details, info->package_name, info->c_filename, o_filename);
                free(o_filename);
                if (!ok) {
                    fprintf(stderr, "Compilation of %s failed\n", info->c_filename);
                    free_module(module);
                    return false;
                }
            }
        }
    }

    free_module(module);
    update_fol_status();
    return true;
}

// Returns true if success, false if error (e.g. module not found, circular dependency)
static bool load_module_recursive(struct LoadDetails *details)
{
    // Check if we have already seen this module...
    struct ModulePathInfo *info = find_module(details->package_loader,
                                              details->importer_package_name,
                                              details->module_name);
    char *full_module_name =
        info ? copy_string_3(info->package_name, "/", details->module_name) : NULL;

    const char *key_out = NULL;
    void *value_out = NULL;
    if (info) {
        hash_table_lookup_2(details->loaded_modules, full_module_name, &key_out, &value_out);
    }

    if (value_out != NULL) {
        // Module was previously loaded. Nothing to do.
        free(full_module_name);
        return true;
    }

    if (key_out != NULL) {
        // Circular dependency.
        report_circular_dependency(details->import_location, details->module_name);
        free(full_module_name);
        return false;
    }

    // The module is now loading
    if (info) {
        hash_table_insert(details->loaded_modules, full_module_name, NULL);
    } else {
        free(full_module_name);
    }

    // Load the module
    return load_module_from_disk(details, info);
}

static void free_all_strings(struct StringNode *strings)
{
    while (strings) {
        free((char*)strings->ptr);
        struct StringNode *to_free = strings;
        strings = strings->next;
        free(to_free);
    }
}

bool compile(struct CompileOptions *options)
{
    struct LoadDetails details;
    details.strings = NULL;

    const char *root_prefix = options->root_package_prefix ? options->root_package_prefix : "";

    details.package_loader = alloc_package_loader(options->pkg_config_cmd);
    if (!load_root_package_and_dependencies(details.package_loader,
                                            root_prefix,
                                            options->search_path)) {
        free_package_loader(details.package_loader);
        return false;
    }

    if (options->output_prefix) {
        details.output_prefix = options->output_prefix;
    } else {
        char *str = copy_string_2(root_prefix, "build/");
        add_string(&details.strings, str);
        details.output_prefix = str;
    }

    if (!maybe_mkdir(details.output_prefix, 0777)) {
        fprintf(stderr, "Output path '%s' doesn't exist and couldn't be created\n", details.output_prefix);
        free_package_loader(details.package_loader);
        free_all_strings(details.strings);
        return false;
    }

    details.loaded_modules = new_hash_table();
    details.renamer_env = new_hash_table();
    details.type_env = new_type_env();
    details.expanded_type_env = new_type_env();
    details.verifier_env = new_verifier_env();
    details.codegen_env = new_codegen_env();

    details.importer_package_name = details.root_package_name =
        get_root_package_name(details.package_loader);


    // Open the cache unless (a) it is disabled or (b) we are only compiling,
    // not verifying (in which case the cache is not needed).
    if (options->cache_mode == CACHE_DISABLED || options->mode == CM_COMPILE) {
        details.cache_db = NULL;
    } else {
        details.cache_db = open_cache_db(details.output_prefix);
    }

    start_fol_runner(details.cache_db,
                     options->provers,
                     options->config_filename,
                     options->max_child_processes,
                     options->continue_after_verify_error);

    details.import_location = g_no_location;
    details.compile_mode = options->mode;

    if (options->requested_modules && options->mode == CM_COMPILE) {
        fatal_error("Requested modules not currently supported for CM_COMPILE");
    }

    details.requested_modules = options->requested_modules;
    details.show_progress = options->show_progress;
    details.create_debug_files = options->create_debug_files;

    details.main_module_name = get_root_main_module(details.package_loader);
    details.main_function_name = get_root_main_function(details.package_loader);
    details.obj_files = NULL;

    details.cc_cmd = options->cc_cmd;
    details.ld_cmd = options->ld_cmd;
    details.cflags = options->cflags;
    details.libs = options->libs;
    details.run_c_compiler = options->run_c_compiler;
    details.print_c_compiler_commands = options->print_c_compiler_commands;

    bool success = true;
    if (options->requested_modules == NULL) {
        for (struct NameList * names = get_root_exported_modules(details.package_loader); success && names; names = names->next) {
            details.module_name = names->name;
            success = load_module_recursive(&details);
        }
        if (details.main_module_name && success) {
            details.module_name = details.main_module_name;
            success = load_module_recursive(&details);
        }
    } else {
        for (struct NameList *names = options->requested_modules; success && names; names = names->next) {
            details.module_name = names->name;
            success = load_module_recursive(&details);
        }
    }

    // Wait for FOL runner to complete, and then get final status
    wait_fol_complete();
    success = success && !fol_error_found();
    stop_fol_runner();

    // If everything is ok we can now link
    // Note: Linking only happens when a main_module is defined.
    if (options->mode == CM_COMPILE
    && options->run_c_compiler
    && success
    && details.obj_files != NULL
    && details.main_module_name) {
        success = run_linker(&details);
    }

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

    free_all_strings(details.strings);
    free_name_list(details.obj_files);

    free_package_loader(details.package_loader);

    return success;
}

void free_compile_options(struct CompileOptions *copt)
{
    if (copt) {
        free((char*)copt->config_filename);
        free((char*)copt->pkg_config_cmd);
        free((char*)copt->cc_cmd);
        free((char*)copt->ld_cmd);
        free_name_list(copt->cflags);
        free_name_list(copt->libs);
        free((char*)copt->root_package_prefix);
        free((char*)copt->output_prefix);
        free_name_list(copt->search_path);
        free_name_list(copt->requested_modules);
        free_prover_config(copt->provers);
        free(copt);
    }
}
