/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


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
    const char *filename;
    const char *output_path;
    bool quiet;
    bool debug;
    bool verify_continue;
    int verify_timeout;
    bool generate_main;
    bool auto_main;
};

static void print_usage_and_exit(char **argv)
{
    fprintf(stderr, "Usage: %s <options> <filename>\n", argv[0]);
    fprintf(stderr, "Options:\n");
    fprintf(stderr, "  -c, --compile:          Compile the given file (and all its dependencies) to .s files\n");
    fprintf(stderr, "  -v, --verify:           Verify the code in the specified file, but not the imports\n");
    fprintf(stderr, "  -V, --verify-all:       Verify the code in the specified file and all imports\n");
    fprintf(stderr, "  -o, --output-path:      Set output path (default is same folder as the input)\n");
    fprintf(stderr, "  -q, --quiet:            Don't print progress messages while verifying\n");
    fprintf(stderr, "      --verify-continue:  Don't stop after the first verification error\n");
    fprintf(stderr, "  -t, --verify-timeout:   Set verification timeout in seconds (default = 60)\n");
    fprintf(stderr, "      --main:             Always generate the C 'main' function\n");
    fprintf(stderr, "      --no-main:          Never generate the C 'main' function\n");
    fprintf(stderr, "  -d, --debug:            Create debug output files\n");
    fprintf(stderr, "  -h, --help:             Show help\n");
    exit(1);
}


static void ensure_mode_not_set(struct Options *options, char **argv)
{
    if (options->mode_set) {
        fprintf(stderr, "%s: Options -c, -v and -V are mutually exclusive\n", argv[0]);
        exit(1);
    }
}

static void parse_options(int argc, char **argv, struct Options *options)
{
    memset(options, 0, sizeof(struct Options));
    options->verify_timeout = 60;
    options->auto_main = true;

    enum { OPT_VERIFY_CONTINUE = 2, OPT_MAIN = 3, OPT_NO_MAIN = 4 };

    static struct option long_options[] = {
        {"help",            no_argument,       NULL, 'h'},
        {"compile",         no_argument,       NULL, 'c'},
        {"verify",          no_argument,       NULL, 'v'},
        {"verify-all",      no_argument,       NULL, 'V'},
        {"output-path",     required_argument, NULL, 'o'},
        {"quiet",           no_argument,       NULL, 'q'},
        {"verify-continue", no_argument,       NULL, OPT_VERIFY_CONTINUE},
        {"verify-timeout",  required_argument, NULL, 't'},
        {"main",            no_argument,       NULL, OPT_MAIN},
        {"no-main",         no_argument,       NULL, OPT_NO_MAIN},
        {"debug",           no_argument,       NULL, 'd'},
    };

    bool error_found = false;

    while (true) {
        int option_index = 0;
        int c = getopt_long(argc, argv, "hcvVo:qt:d", long_options, &option_index);

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

        case 'V':
            ensure_mode_not_set(options, argv);
            options->mode = CM_VERIFY_ALL;
            options->mode_set = true;
            break;

        case 'o':
            if (options->output_path) {
                fprintf(stderr, "Only one output path can be specified at a time\n");
                exit(1);
            }
            options->output_path = optarg;
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

        case OPT_MAIN:
            options->auto_main = false;
            options->generate_main = true;
            break;

        case OPT_NO_MAIN:
            options->auto_main = false;
            options->generate_main = false;
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
        options->filename = argv[optind++];
        if (optind < argc) {
            fprintf(stderr, "%s: Too many command line arguments\n", argv[0]);
            exit(1);
        }
    }

    if (options->filename == NULL) {
        fprintf(stderr, "%s: Filename required\n", argv[0]);
        exit(1);
    }

    if (!options->mode_set) {
        fprintf(stderr, "%s: Nothing to do. Please specify one of -c, -v, or -V.\n", argv[0]);
        exit(1);
    }
}

char * make_output_prefix(const char *path)
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

int main(int argc, char **argv)
{
    struct Options options;
    parse_options(argc, argv, &options);

    // Compile
    struct CompileOptions copt;
    copt.filename = options.filename;
    copt.output_prefix = make_output_prefix(options.output_path);
    copt.mode = options.mode;
    copt.show_progress = !options.quiet;
    copt.create_debug_files = options.debug;
    copt.continue_after_verify_error = options.verify_continue;
    copt.verify_timeout_seconds = options.verify_timeout;
    copt.generate_main = options.generate_main;
    copt.auto_main = options.auto_main;
    bool success = compile(&copt);
    free((char*)copt.output_prefix);

    if ((options.mode == CM_VERIFY || options.mode == CM_VERIFY_ALL) && !options.quiet) {
        if (success) {
            fprintf(stderr, "Verification successful\n");
        } else {
            fprintf(stderr, "Verification failed\n");
        }
    }

    return success ? 0 : 1;
}
