/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "compiler.h"
#include "config_file.h"
#include "error.h"
#include "util.h"

#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void print_usage_and_exit(char **argv)
{
    printf("Usage: %s <options>\n", argv[0]);
    printf("Options:\n");
    printf("  -c, --compile:          Compile to .c files\n");
    printf("  -v, --verify:           Verify the code\n");
    printf("  -r, --root:             Set compile root dir (default '.')\n");
    printf("  -p, --package-path:     Add package search path\n");
    printf("  -o, --output-path:      Set output path (default is 'build' under compile root dir)\n");
    printf("  -m, --module:           Verify a specific module (default is to verify all relevant modules)\n");
    printf("  -q, --quiet:            Don't print progress messages while verifying\n");
    printf("      --verify-continue:  Don't stop after the first verification error\n");
    printf("  -t, --verify-timeout:   Set verification timeout in seconds (default = 60)\n");
    printf("      --no-cache:         Disable the verification cache ('babylon.cache' file)\n");
    printf("  -d, --debug:            Create debug output files\n");
    printf("  -h, --help:             Show help\n");
    exit(1);
}

static void error_compile_mode_already_set(char **argv)
{
    fprintf(stderr, "%s: Options -c and -v are mutually exclusive\n", argv[0]);
    exit(1);
}

static void parse_options(int argc, char **argv, struct CompileOptions *copt)
{
    enum { OPT_VERIFY_CONTINUE = 1,
           OPT_NO_CACHE = 2 };

    static struct option long_options[] = {
        {"help",            no_argument,       NULL, 'h'},
        {"compile",         no_argument,       NULL, 'c'},
        {"verify",          no_argument,       NULL, 'v'},
        {"root",            required_argument, NULL, 'r'},
        {"package-path",    required_argument, NULL, 'p'},
        {"output-path",     required_argument, NULL, 'o'},
        {"quiet",           no_argument,       NULL, 'q'},
        {"verify-continue", no_argument,       NULL, OPT_VERIFY_CONTINUE},
        {"verify-timeout",  required_argument, NULL, 't'},
        {"no-cache",        no_argument,       NULL, OPT_NO_CACHE},
        {"debug",           no_argument,       NULL, 'd'},
    };

    bool compile_mode_set = false;
    bool error_found = false;

    struct NameList **package_paths_tail = &copt->search_path;
    struct NameList **requested_modules_tail = &copt->requested_modules;

    while (true) {
        int option_index = 0;
        int c = getopt_long(argc, argv, "hcvr:p:o:m:qt:d", long_options, &option_index);

        if (c == -1) {
            break;
        }

        switch (c) {
        case 'h':
            print_usage_and_exit(argv);
            break;

        case 'c':
            if (compile_mode_set) {
                error_compile_mode_already_set(argv);
            }
            copt->mode = CM_COMPILE;
            compile_mode_set = true;
            break;

        case 'v':
            if (compile_mode_set) {
                error_compile_mode_already_set(argv);
            }
            copt->mode = CM_VERIFY;
            compile_mode_set = true;
            break;

        case 'r':
            if (copt->root_package_prefix) {
                fprintf(stderr, "Only one root path can be specified at a time\n");
                exit(1);
            }
            copt->root_package_prefix = copy_string(optarg);
            break;

        case 'p':
            {
                struct NameList *node = alloc(sizeof(struct NameList));
                node->name = copy_string(optarg);
                node->next = *package_paths_tail;
                *package_paths_tail = node;
                package_paths_tail = &node->next;
            }
            break;

        case 'o':
            if (copt->output_prefix) {
                fprintf(stderr, "Only one output path can be specified at a time\n");
                exit(1);
            }
            copt->output_prefix = copy_string(optarg);
            break;

        case 'm':
            {
                struct NameList *node = alloc(sizeof(struct NameList));
                node->name = copy_string(optarg);
                node->next = *requested_modules_tail;
                *requested_modules_tail = node;
                requested_modules_tail = &node->next;
            }
            break;

        case 'q':
            copt->show_progress = false;
            break;

        case OPT_VERIFY_CONTINUE:
            copt->continue_after_verify_error = true;
            break;

        case 't':
            {
                int timeout = atoi(optarg);
                if (timeout <= 0) {
                    fprintf(stderr, "Invalid timeout value: %s\n", optarg);
                    exit(1);
                }

                // overwrite the timeout for every prover
                for (struct ProverConfig *pr = copt->provers; pr; pr = pr->next) {
                    pr->timeout = timeout;
                }
            }
            break;

        case OPT_NO_CACHE:
            copt->cache_mode = CACHE_DISABLED;
            break;

        case 'd':
            copt->create_debug_files = true;
            break;

        case '?':
            // getopt_long already printed an error message
            error_found = true;
            break;

        default:
            fatal_error("unexpected result from getopt_long");
        }
    }

    if (error_found) {
        exit(1);
    }

    if (optind < argc) {
        fprintf(stderr, "%s: Too many command line arguments\n", argv[0]);
        exit(1);
    }

    if (!compile_mode_set) {
        fprintf(stderr, "%s: Nothing to do. Please specify one of -c or -v.\n", argv[0]);
        exit(1);
    }

    if (copt->mode == CM_COMPILE && copt->requested_modules != NULL) {
        fprintf(stderr, "%s: -m option is incompatible with -c\n", argv[0]);
        exit(1);
    }
}

static void add_trailing_slash(const char **path)
{
    // A NULL path is left unchanged.
    if (*path != NULL) {
        // If the path is non-empty and doesn't end in "/", then append "/".
        size_t len = strlen(*path);
        if (len > 0 && (*path)[len - 1] != '/') {
            char *path2 = copy_string_2(*path, "/");
            free((char*)*path);
            *path = path2;
        }
    }
}

static void add_trailing_slash_namelist(struct NameList *dirs)
{
    for (struct NameList *dir = dirs; dir; dir = dir->next) {
        add_trailing_slash(&dir->name);
    }
}

static void free_string_array(const char **arr)
{
    void *mem = arr;
    while (*arr) {
        free((char*)*arr);
        arr++;
    }
    free(mem);
}

int main(int argc, char **argv)
{
    // Read config file.
    struct CompilerConfig *cfg = load_config_file();

    // Transfer config to CompileOptions.
    struct CompileOptions copt;
    copt.pkg_config_cmd = cfg->pkg_config;
    copt.cc_cmd = cfg->c_compiler;
    copt.ld_cmd = cfg->linker;
    copt.cflags = cfg->cflags;
    copt.libs = cfg->libs;
    copt.root_package_prefix = NULL;   // Set via cmd line, -r
    copt.output_prefix = NULL;         // Set via cmd line, -o
    copt.search_path = cfg->package_paths;   // Augmented via cmd line, -p
    copt.requested_modules = NULL;     // Set via cmd line, -m
    // NOTE: copt.mode is set via cmd line (-c or -v), and not initialized here
    copt.cache_mode = (cfg->use_verifier_cache ? CACHE_ENABLED : CACHE_DISABLED); // Can be overridden by cmd line, --no-cache
    copt.show_progress = true;         // Set via cmd line, -q
    copt.create_debug_files = false;   // Set via cmd line, -d
    copt.continue_after_verify_error = false;    // Set via cmd line, --verify-continue
    copt.max_child_processes = cfg->max_verifier_processes;
    copt.provers = cfg->provers;

    // CompilerConfig is no longer needed after this point.
    free(cfg);

    // Read command line arguments, adding the results to the CompileOptions.
    parse_options(argc, argv, &copt);

    // Make sure the "path" settings all have a trailing slash if required
    add_trailing_slash(&copt.root_package_prefix);
    add_trailing_slash(&copt.output_prefix);
    add_trailing_slash_namelist(copt.search_path);

    // Run the compiler.
    bool success = compile(&copt);

    // Free config/options that are no longer required.
    free((char*)copt.pkg_config_cmd);
    free((char*)copt.cc_cmd);
    free((char*)copt.ld_cmd);
    free_name_list(copt.cflags);
    free_name_list(copt.libs);
    free((char*)copt.root_package_prefix);
    free((char*)copt.output_prefix);
    free_name_list(copt.search_path);
    free_name_list(copt.requested_modules);

    struct ProverConfig *pr = copt.provers;
    while (pr) {
        struct ProverConfig *next = pr->next;
        free((char*)pr->name);
        free_string_array(pr->command_and_arguments);
        free(pr);
        pr = next;
    }

    // Report success or failure on stderr (for verification jobs).
    if ((copt.mode == CM_VERIFY) && copt.show_progress) {
        if (success) {
            fprintf(stderr, "Verification successful\n");
        } else {
            fprintf(stderr, "Verification failed\n");
        }
    }

    // Return correct exit code.
    return success ? 0 : 1;
}
