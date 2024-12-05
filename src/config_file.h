/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef CONFIG_FILE_H
#define CONFIG_FILE_H

#include "util.h"

#include <stdbool.h>

struct ProverConfig {
    struct ProverConfig *next;
    const char *name;
    const char **command_and_arguments;  // terminated by a NULL char* pointer

    bool show_stderr;
    bool ignore_empty_output;
    bool ignore_exit_status;

    int timeout;   // in seconds
    int signal;    // signal number
    int kill_timeout;  // in seconds
};

struct CompilerConfig {
    const char *config_filename;

    // [packages] section
    struct NameList *package_paths;

    // [c-compiler] section
    const char *c_compiler;
    const char *linker;
    struct NameList *cflags;
    struct NameList *libs;
    const char *pkg_config;

    // [verifier] section
    bool use_verifier_cache;
    int max_verifier_processes;

    // [provers] section
    struct ProverConfig *provers;
};

struct CompilerConfig *load_config_file();

void free_prover_config(struct ProverConfig *p);
void free_compiler_config(struct CompilerConfig *cfg);

#endif
