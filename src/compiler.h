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
    CM_VERIFY,
    CM_VERIFY_ALL
};

enum CacheMode {
    CACHE_DISABLED,
    CACHE_ENABLED
};

struct CompileOptions {
    const char *filename;
    const char *output_prefix;
    enum CompileMode mode;
    enum CacheMode cache_mode;
    bool show_progress;
    bool create_debug_files;
    bool continue_after_verify_error;
    int verify_timeout_seconds;
    bool generate_main;
    bool auto_main;
};


//
// Loads and "compiles" a module (and its imports) from the filesystem.
//
//  - The filename for the root module must be given.
//
//  - The root module, together with any imported modules, are loaded from the filesystem.
//     - For now, there is no "search path", modules are looked for in the current directory.
//
//  - Returns true if successful, false if errors.
//
//  - For now only verification OR compilation can be done, not both. Verification just
//    prints errors and returns a pass/fail result. Compilation additionally creates .s
//    files alongside each input file.
//
bool compile(struct CompileOptions *options);


#endif
