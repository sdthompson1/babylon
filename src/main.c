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
#include "version.h"

#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//------------------------------------------------------------------------
// Subcommand Names

enum Subcommand {
    CMD_UNKNOWN,
    CMD_HELP,
    CMD_COMPILE,
    CMD_VERIFY,
    CMD_BUILD,
    CMD_TRANSLATE,
    CMD_CHECK_CONFIG,
    CMD_VERSION
};

enum Subcommand string_to_subcommand(const char *p)
{
    if (strcmp(p, "help") == 0) {
        return CMD_HELP;
    } else if (strcmp(p, "compile") == 0) {
        return CMD_COMPILE;
    } else if (strcmp(p, "verify") == 0) {
        return CMD_VERIFY;
    } else if (strcmp(p, "build") == 0) {
        return CMD_BUILD;
    } else if (strcmp(p, "translate") == 0) {
        return CMD_TRANSLATE;
    } else if (strcmp(p, "check-config") == 0) {
        return CMD_CHECK_CONFIG;
    } else if (strcmp(p, "version") == 0) {
        return CMD_VERSION;
    } else {
        return CMD_UNKNOWN;
    }
}

//------------------------------------------------------------------------
// Help Subcommand

static void print_general_help(FILE *file, char **argv)
{
    fprintf(file, "Usage: %s <command> [<options>]\n", argv[0]);
    fprintf(file, "\n");
    fprintf(file, "Available commands:\n");
    fprintf(file, "  compile        Compile a Babylon package to object code or an executable\n");
    fprintf(file, "  verify         Verify a Babylon package\n");
    fprintf(file, "  build          Combination of 'compile' and 'verify'\n");
    fprintf(file, "  translate      Create .c files but don't invoke the C compiler\n");
    fprintf(file, "  check-config   Run some checks on the compiler config file (babylon.toml)\n");
    fprintf(file, "  version        Print compiler version\n");
    fprintf(file, "\n");
    fprintf(file, "Use '%s <command> --help' for help about a specific command.\n", argv[0]);
    fprintf(file, "\n");
}

static void print_path_options(FILE *file)
{
    fprintf(file, "  -r, --root <path>            Specify build root directory (default '.')\n");
    fprintf(file, "  -p, --package-path <path>    Specify a directory to search for dependency packages\n");
    fprintf(file, "                               (multiple -p options may be given)\n");
    fprintf(file, "  -o, --output-path <path>     Set the output path (default: '<build-root>/build')\n");
}

static void print_compile_options(FILE *file)
{
    fprintf(file, "  -v, --verbose                Print compiler and linker commands as they are executed\n");
}

static void print_debug_options(FILE *file)
{
    fprintf(file, "  -d, --debug                  Create debug output files\n");
}

static void print_compile_or_translate_usage(FILE *file, char **argv, enum Subcommand cmd)
{
    fprintf(file, "Usage: %s %s [<options>]\n", argv[0], cmd == CMD_COMPILE ? "compile" : "translate");
    fprintf(file, "\n");
    fprintf(file, "Options:\n");
    print_path_options(file);  // -r, -p, -o
    if (cmd == CMD_COMPILE) {
        print_compile_options(file);  // -v
    }
    print_debug_options(file);  // -d
    fprintf(file, "\n");
}

static void print_verify_usage(FILE *file, char **argv)
{
    fprintf(file, "Usage: %s verify [<options>]\n", argv[0]);
    fprintf(file, "\n");
    fprintf(file, "Options:\n");
    print_path_options(file);  // -p, -o
    fprintf(file,
            "  -m, --module <module-name>   Verify only the specified module(s)\n"
            "                               (default is to verify all relevant modules)\n"
            "  -q, --quiet                  Suppress progress messages\n"
            "      --continue               Continue verifying after first error\n"
            "  -t, --timeout <seconds>      Set prover timeout\n"
            "      --no-cache               Do not use the cache\n");
    fprintf(file, "\n");
}

// Print help on stdout (or an error msg on stderr if cmd is CMD_UNKNOWN).
// 'cmd_name' only needs to be non-NULL if cmd == CMD_UNKNOWN.
static bool print_help_for_subcommand(enum Subcommand cmd, char **argv, const char *cmd_name)
{
    switch (cmd) {
    case CMD_UNKNOWN:
        fprintf(stderr, "Unknown command: %s\n", cmd_name);
        fprintf(stderr, "Try '%s --help' for a list of valid commands.\n", argv[0]);
        return false;

    case CMD_HELP:
        // We don't have anything specific for 'help help'. Just print the general help.
        print_general_help(stdout, argv);
        break;

    case CMD_COMPILE:
        printf("Compile a Babylon package to object files (*.o) or to an executable binary.\n\n");
        print_compile_or_translate_usage(stdout, argv, cmd);
        break;

    case CMD_VERIFY:
        printf("Verify a Babylon package.\n\n");
        print_verify_usage(stdout, argv);
        break;

    case CMD_BUILD:
        printf("Verify and then compile a Babylon package.\n\n");
        // TODO: Print usage
        break;

    case CMD_TRANSLATE:
        printf("Translate a Babylon package to C code (*.c files).\n\n");
        print_compile_or_translate_usage(stdout, argv, cmd);
        break;

    case CMD_CHECK_CONFIG:
        printf("Check that the compiler configuration file is valid.\n\n");
        // TODO: Print usage
        break;

    case CMD_VERSION:
        printf("Report the compiler version.\n\n");
        printf("Usage: %s version\n\n", argv[0]);
        break;
    }

    return true;
}

static bool help_subcommand(int argc, char **argv)
{
    bool first = true;
    for (int i = 1; i < argc; ++i) {
        if (argv[i][0] != '-') {
            if (first) {
                // this is the 'help' keyword
                first = false;
            } else {
                // this is the subcommand they want help with
                return print_help_for_subcommand(string_to_subcommand(argv[i]), argv, argv[i]);
            }
        }
    }

    // print the general help
    print_general_help(stdout, argv);
    return true;
}

//------------------------------------------------------------------------
// Compile / Translate Subcommands

static void parse_r_argument(struct CompileOptions *copt)
{
    if (copt->root_package_prefix) {
        fprintf(stderr, "Build root (-r) can only be specified once\n");
        exit(1);
    }
    copt->root_package_prefix = copy_string(optarg);
}

static void parse_p_argument(struct CompileOptions *copt,
                             struct NameList ***tail)
{
    struct NameList *node = alloc(sizeof(struct NameList));
    node->name = copy_string(optarg);
    node->next = **tail;
    **tail = node;
    *tail = &node->next;
}

static void parse_o_argument(struct CompileOptions *copt)
{
    if (copt->output_prefix) {
        fprintf(stderr, "Only one output path can be specified at a time\n");
        exit(1);
    }
    copt->output_prefix = copy_string(optarg);
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

static void check_unwanted_args(int argc, char **argv)
{
    ++optind;  // Skip the subcommand name
    if (optind < argc) {
        fprintf(stderr, "Unexpected argument: %s\n", argv[optind]);
        exit(1);
    }
}

static void adjust_compile_options(struct CompileOptions *copt)
{
    // Make sure the "path" settings all have a trailing slash if required
    add_trailing_slash(&copt->root_package_prefix);
    add_trailing_slash(&copt->output_prefix);
    add_trailing_slash_namelist(copt->search_path);
}

// This will exit on error, or if --help is used.
static void parse_compile_or_translate_options_or_exit(int argc, char **argv,
                                                       struct CompileOptions *copt,
                                                       enum Subcommand cmd)
{
    static struct option long_options[] = {
        {"help",            no_argument,       NULL, 'h'},
        {"root",            required_argument, NULL, 'r'},
        {"package-path",    required_argument, NULL, 'p'},
        {"output-path",     required_argument, NULL, 'o'},
        {"verbose",         no_argument,       NULL, 'v'},
        {"debug",           no_argument,       NULL, 'd'},
        {0,                 0,                 0,    0  }
    };

    struct NameList **package_paths_tail = &copt->search_path;

    while (true) {
        int c = getopt_long(argc, argv, "hr:p:o:vd", long_options, NULL);

        if (c == -1) {
            break;
        }

        switch (c) {
        case 'h':
            print_help_for_subcommand(cmd, argv, NULL);
            exit(0);

        case 'r':
            parse_r_argument(copt);
            break;

        case 'p':
            parse_p_argument(copt, &package_paths_tail);
            break;

        case 'o':
            parse_o_argument(copt);
            break;

        case 'v':
            copt->print_c_compiler_commands = true;
            break;

        case 'd':
            copt->create_debug_files = true;
            break;

        case '?':
            // getopt_long already printed an error message
            exit(1);

        default:
            fatal_error("unexpected result from getopt_long");
        }
    }

    check_unwanted_args(argc, argv);
    adjust_compile_options(copt);
}

static bool compile_or_translate_subcommand(int argc, char **argv,
                                            struct CompileOptions *copt,
                                            enum Subcommand cmd)
{
    copt->mode = CM_COMPILE;
    copt->run_c_compiler = (cmd == CMD_COMPILE);

    parse_compile_or_translate_options_or_exit(argc, argv, copt, cmd);

    return compile(copt);
}

//------------------------------------------------------------------------
// Verify Subcommand

static void parse_verify_options_or_exit(int argc, char **argv,
                                         struct CompileOptions *copt)
{
    enum { OPT_CONTINUE = 1, OPT_NO_CACHE = 2 };

    static struct option long_options[] = {
        {"help",            no_argument,       NULL, 'h'},
        {"root",            required_argument, NULL, 'r'},
        {"package-path",    required_argument, NULL, 'p'},
        {"output-path",     required_argument, NULL, 'o'},
        {"module",          required_argument, NULL, 'm'},
        {"quiet",           no_argument,       NULL, 'q'},
        {"continue",        no_argument,       NULL, OPT_CONTINUE},
        {"timeout",         required_argument, NULL, 't'},
        {"no-cache",        no_argument,       NULL, OPT_NO_CACHE},
        {"debug",           no_argument,       NULL, 'd'},
        {0,                 0,                 0,    0  }
    };

    struct NameList **package_paths_tail = &copt->search_path;
    struct NameList **requested_modules_tail = &copt->requested_modules;

    while (true) {
        int c = getopt_long(argc, argv, "hr:p:o:vd", long_options, NULL);

        if (c == -1) {
            break;
        }

        switch (c) {
        case 'h':
            print_help_for_subcommand(CMD_VERIFY, argv, NULL);
            exit(0);

        case 'r':
            parse_r_argument(copt);
            break;

        case 'p':
            parse_p_argument(copt, &package_paths_tail);
            break;

        case 'o':
            parse_o_argument(copt);
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

        case OPT_CONTINUE:
            copt->continue_after_verify_error = true;
            break;

        case 't':
            {
                int timeout = atoi(optarg);
                if (timeout <= 0) {
                    fprintf(stderr, "Invalid timeout value: %s\n", optarg);
                    exit(1);
                }

                // Overwrite timeout for every prover
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
            exit(1);

        default:
            fatal_error("unexpected result from getopt_long");
        }
    }

    check_unwanted_args(argc, argv);
    adjust_compile_options(copt);
}

static bool verify_subcommand(int argc, char **argv, struct CompileOptions *copt)
{
    copt->mode = CM_VERIFY;

    parse_verify_options_or_exit(argc, argv, copt);

    bool success = compile(copt);

    if (copt->show_progress) {
        if (success) {
            fprintf(stderr, "Verification successful\n");
        } else {
            fprintf(stderr, "Verification failed\n");
        }
    }

    return success;
}

//------------------------------------------------------------------------
// Main program

static void print_version()
{
    printf("bab %s\n", VERSION_STRING);
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
    copt.root_package_prefix = NULL;   // Set via cmd line
    copt.output_prefix = NULL;         // Set via cmd line, -o
    copt.search_path = cfg->package_paths;   // Augmented via cmd line, -p
    copt.requested_modules = NULL;     // Set via cmd line, -m
    // NOTE: copt.mode is set via cmd line, and not initialized here
    copt.cache_mode = (cfg->use_verifier_cache ? CACHE_ENABLED : CACHE_DISABLED); // Can be overridden by cmd line, --no-cache
    copt.show_progress = true;         // Set via cmd line, -q
    copt.create_debug_files = false;   // Set via cmd line, -d
    copt.continue_after_verify_error = false;    // Set via cmd line, --continue
    copt.max_child_processes = cfg->max_verifier_processes;
    copt.provers = cfg->provers;
    copt.run_c_compiler = false;
    copt.print_c_compiler_commands = false;

    // CompilerConfig is no longer needed after this point.
    free(cfg);

    // Determine the subcommand in use.
    int idx;
    for (idx = 1; idx < argc; ++idx) {
        if (argv[idx][0] != '-') {
            break;
        }
    }
    if (idx == argc) {
        // No subcommand specified.
        if (argc == 1 || strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0) {
            // "bab" or "bab -h" or "bab --help"
            print_general_help(stdout, argv);
            exit(0);
        } else if (strcmp(argv[1], "-V") == 0 || strcmp(argv[1], "--version") == 0) {
            // "bab -V" or "bab --version"
            print_version();
            exit(0);
        } else {
            // "bab --something-else"
            fprintf(stderr, "Unexpected argument: %s\n", argv[1]);
            fprintf(stderr, "Try '%s --help' for help.\n", argv[0]);
            exit(1);
        }
    }

    // Execute the subcommand.
    bool success = false;
    enum Subcommand cmd = string_to_subcommand(argv[idx]);
    switch (cmd) {
    case CMD_UNKNOWN:
        // This prints the "unknown command" message
        print_help_for_subcommand(cmd, argv, argv[idx]);
        break;

    case CMD_HELP:
        success = help_subcommand(argc, argv);
        break;

    case CMD_COMPILE:
    case CMD_TRANSLATE:
        success = compile_or_translate_subcommand(argc, argv, &copt, cmd);
        break;

    case CMD_VERIFY:
        success = verify_subcommand(argc, argv, &copt);
        break;

    case CMD_BUILD:
        fprintf(stderr, "TODO: 'build' command is not implemented yet.\n");
        break;

    case CMD_CHECK_CONFIG:
        fprintf(stderr, "TODO: 'check-config' command is not implemented yet\n");
        break;

    case CMD_VERSION:
        print_version();
        success = true;
        break;
    }

    // Free the config.
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

    // Return correct exit code.
    return success ? 0 : 1;
}
