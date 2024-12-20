/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef COMPILER_H
#define COMPILER_H

#include <stdbool.h>
#include <stdint.h>

struct Env;
struct HashTable;

struct CompileResult;

enum CacheMode {
    CACHE_DISABLED,
    CACHE_ENABLED
};

struct CompileOptions {
    const char *config_filename;   // for error messages

    const char *pkg_config_cmd;
    const char *cc_cmd;
    const char *ld_cmd;
    struct NameList *cflags;
    struct NameList *libs;

    const char *root_package_prefix;  // optional (NULL means "")
    const char *output_prefix;   // optional (NULL means root_package_prefix + "build/")
    struct NameList *search_path;  // search path for dependent packages (each entry is a "prefix")

    // The list of module names to compile/verify.
    // Empty means do everything accessible from main_module and exported_modules.
    // NOTE: Currently this is only supported when do_compile=false. Otherwise it must be empty.
    struct NameList *requested_modules;

    // do_compile and do_verify cannot both be false.
    bool do_compile;
    bool do_verify;

    enum CacheMode cache_mode;
    bool show_progress;
    bool create_debug_files;
    bool continue_after_verify_error;
    int max_child_processes;
    struct ProverConfig *provers;

    bool run_c_compiler;
    bool print_c_compiler_commands;
};

void free_compile_options(struct CompileOptions *copt);

//
// Loads and "compiles" a module (and its imports) from the filesystem.
//
//  - The "prefix" for the package.toml file for the root package must be given.
//     - This is either an empty string to use the current directory, or a relative
//       or absolute path ending in a slash.
//
//  - The root package, together with any dependencies, are loaded from the filesystem.
//
//  - Returns true if successful, false if errors.
//
//  - For now only verification OR compilation can be done, not both. Verification just
//    prints errors and returns a pass/fail result. Compilation additionally creates .b.c
//    files alongside each input file.
//
bool compile(struct CompileOptions *options);


#endif
