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

enum CompileMode {
    CM_COMPILE,
    CM_VERIFY
};

enum CacheMode {
    CACHE_DISABLED,
    CACHE_ENABLED
};

struct CompileOptions {
    const char *root_package_prefix;  // optional (NULL means "")
    const char *output_prefix;   // optional (NULL means root_package_prefix + "build/")
    struct NameList *search_path;  // search path for dependent packages (each entry is a "prefix")

    // The list of module names to compile/verify.
    // Empty means do everything accessible from main_module and exported_modules.
    // NOTE: Currently this is only supported for CM_VERIFY. For CM_COMPILE it must be empty.
    struct NameList *requested_modules;

    enum CompileMode mode;
    enum CacheMode cache_mode;
    bool show_progress;
    bool create_debug_files;
    bool continue_after_verify_error;
    int verify_timeout_seconds;
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
bool compile(struct CompileOptions *options);


#endif
