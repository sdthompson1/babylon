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

    // If this is non-NULL then a module called "Main" in the root package will
    // use this filename instead of the usual "Main.b". (Used for the fuzzing mode.)
    const char *main_filename_override;
};

void free_compile_options(struct CompileOptions *copt);

// Possible results of a "compile" call
enum CompileResult {
    CR_SUCCESS = 0,
    CR_LEX_ERROR = 1,      // lexer failed, or couldn't open input files, or package.toml problem
    CR_PARSE_ERROR = 2,    // parser failed
    CR_RENAME_ERROR = 3,   // renamer failed, or module name mismatch filename, or circular import
    CR_TYPE_ERROR = 4,     // typechecker failed, or main function has wrong type
    CR_VERIFY_ERROR = 5,   // verifier failed
    CR_COMPILE_ERROR = 6   // couldn't open .c output file, or external compiler or linker command failed
};

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
enum CompileResult compile(struct CompileOptions *options);


#endif
