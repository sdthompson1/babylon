/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "compiler.h"
#include "error.h"
#include "util.h"

#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct Options {
    bool mode_set;
    enum CompileMode mode;
    enum CacheMode cache_mode;
    const char *root_path;

    struct NameList *package_paths;
    struct NameList *requested_modules;
    struct NameList **package_paths_tail;
    struct NameList **requested_modules_tail;

    const char *output_path;
    bool quiet;
    bool debug;
    bool verify_continue;
    int verify_timeout;
};

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


static void ensure_mode_not_set(struct Options *options, char **argv)
{
    if (options->mode_set) {
        fprintf(stderr, "%s: Options -c and -v are mutually exclusive\n", argv[0]);
        exit(1);
    }
}

static void parse_options(int argc, char **argv, struct Options *options)
{
    memset(options, 0, sizeof(struct Options));
    options->cache_mode = CACHE_ENABLED;
    options->verify_timeout = 60;

    options->package_paths_tail = &options->package_paths;
    options->requested_modules_tail = &options->requested_modules;

    enum { OPT_VERIFY_CONTINUE = 2,
           OPT_NO_CACHE = 5 };

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

    bool error_found = false;

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
            ensure_mode_not_set(options, argv);
            options->mode = CM_COMPILE;
            options->mode_set = true;
            break;

        case 'v':
            ensure_mode_not_set(options, argv);
            options->mode = CM_VERIFY;
            options->mode_set = true;
            break;

        case 'r':
            if (options->root_path) {
                fprintf(stderr, "Only one root path can be specified at a time\n");
                exit(1);
            }
            options->root_path = optarg;
            break;

        case 'p':
            {
                struct NameList *node = alloc(sizeof(struct NameList));
                node->name = copy_string(optarg);
                node->next = NULL;
                *options->package_paths_tail = node;
                options->package_paths_tail = &node->next;
            }
            break;

        case 'o':
            if (options->output_path) {
                fprintf(stderr, "Only one output path can be specified at a time\n");
                exit(1);
            }
            options->output_path = optarg;
            break;

        case 'm':
            {
                struct NameList *node = alloc(sizeof(struct NameList));
                node->name = copy_string(optarg);
                node->next = NULL;
                *options->requested_modules_tail = node;
                options->requested_modules_tail = &node->next;
            }
            break;

        case 'q':
            options->quiet = true;
            break;

        case OPT_VERIFY_CONTINUE:
            options->verify_continue = true;
            break;

        case 't':
            options->verify_timeout = atoi(optarg);
            if (options->verify_timeout <= 0) {
                fprintf(stderr, "Invalid timeout value: %s\n", optarg);
                exit(1);
            }
            break;

        case OPT_NO_CACHE:
            options->cache_mode = CACHE_DISABLED;
            break;

        case 'd':
            options->debug = true;
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

    if (!options->mode_set) {
        fprintf(stderr, "%s: Nothing to do. Please specify one of -c or -v.\n", argv[0]);
        exit(1);
    }
}

static char * make_prefix(const char *path)
{
    if (path == NULL) {
        return NULL;
    }

    size_t len = strlen(path);
    if (len == 0 || path[len - 1] == '/') {
        return copy_string(path);
    } else {
        return copy_string_2(path, "/");
    }
}

static struct NameList * make_search_path(struct NameList *package_dirs)
{
    struct NameList *result = NULL;
    struct NameList **tail = &result;

    for (struct NameList *in = package_dirs; in; in = in->next) {
        struct NameList *out = alloc(sizeof(struct NameList));
        out->name = make_prefix(in->name);
        out->next = NULL;
        *tail = out;
        tail = &out->next;
    }

    return result;
}

int main(int argc, char **argv)
{
    struct Options options;
    parse_options(argc, argv, &options);

    // Compile
    struct CompileOptions copt;
    copt.root_package_prefix = make_prefix(options.root_path);
    copt.output_prefix = make_prefix(options.output_path);
    copt.search_path = make_search_path(options.package_paths); free_name_list(options.package_paths);
    copt.requested_modules = options.mode == CM_COMPILE ? NULL : options.requested_modules;
    copt.mode = options.mode;
    copt.cache_mode = options.cache_mode;
    copt.show_progress = !options.quiet;
    copt.create_debug_files = options.debug;
    copt.continue_after_verify_error = options.verify_continue;
    copt.verify_timeout_seconds = options.verify_timeout;

    bool success = compile(&copt);

    free((char*)copt.output_prefix);
    free((char*)copt.root_package_prefix);
    free_name_list(copt.search_path);
    free_name_list(copt.requested_modules);

    if ((options.mode == CM_VERIFY) && !options.quiet) {
        if (success) {
            fprintf(stderr, "Verification successful\n");
        } else {
            fprintf(stderr, "Verification failed\n");
        }
    }

    return success ? 0 : 1;
}
