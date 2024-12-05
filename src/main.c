/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "check_config.h"
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

const char * subcommand_to_string(enum Subcommand cmd)
{
    switch (cmd) {
    case CMD_UNKNOWN: return "?";
    case CMD_HELP: return "help";
    case CMD_COMPILE: return "compile";
    case CMD_VERIFY: return "verify";
    case CMD_BUILD: return "build";
    case CMD_TRANSLATE: return "translate";
    case CMD_CHECK_CONFIG: return "check-config";
    case CMD_VERSION: return "version";
    }
    fatal_error("bad subcommand value");
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

static void print_compile_or_build_options(FILE *file)
{
    fprintf(file, "  -v, --verbose                Print compiler and linker commands as they are executed\n");
}

static void print_verify_options(FILE *file)
{
    fprintf(file,
            "  -m, --module <module-name>   Verify only the specified module(s)\n"
            "                               (default is to verify all relevant modules)\n");
}

static void print_verify_or_build_options(FILE *file)
{
    fprintf(file,
            "  -q, --quiet                  Suppress progress messages\n"
            "      --continue               Continue verifying after first error\n"
            "  -t, --timeout <seconds>      Set prover timeout\n"
            "      --no-cache               Do not use the cache\n");
}

static void print_debug_options(FILE *file)
{
    fprintf(file, "  -d, --debug                  Create debug output files\n");
}

// This works for compile, translate, verify and build subcommands
static void print_compilation_usage(FILE *file, char **argv, enum Subcommand cmd)
{
    fprintf(file, "Usage: %s %s [<options>]\n", argv[0], subcommand_to_string(cmd));
    fprintf(file, "\n");
    fprintf(file, "Options:\n");
    print_path_options(file);  // -r, -p, -o
    if (cmd == CMD_COMPILE || cmd == CMD_BUILD) {
        print_compile_or_build_options(file);  // -v
    }
    if (cmd == CMD_VERIFY) {
        print_verify_options(file);  // -m
    }
    if (cmd == CMD_VERIFY || cmd == CMD_BUILD) {
        print_verify_or_build_options(file);  // -q, -t, etc.
    }
    print_debug_options(file);  // -d
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
        print_compilation_usage(stdout, argv, cmd);
        break;

    case CMD_VERIFY:
        printf("Verify a Babylon package.\n\n");
        print_compilation_usage(stdout, argv, cmd);
        break;

    case CMD_BUILD:
        printf("Verify and then compile a Babylon package.\n\n");
        print_compilation_usage(stdout, argv, cmd);
        break;

    case CMD_TRANSLATE:
        printf("Translate a Babylon package to C code (*.c files).\n\n");
        print_compilation_usage(stdout, argv, cmd);
        break;

    case CMD_CHECK_CONFIG:
        printf("Check that the compiler configuration file is valid.\n\n");
        printf("Usage: %s check-config\n\n", argv[0]);
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
// Compilation Subcommands (translate, compile, verify, build)

// This "moves" all the settings from cfg to a new CompileOptions struct.
// cfg is not freed, but it is "nulled out".
static struct CompileOptions * transfer_compiler_config(struct CompilerConfig *cfg)
{
    struct CompileOptions *copt = alloc(sizeof(struct CompileOptions));
    copt->config_filename = cfg->config_filename; cfg->config_filename = NULL;
    copt->pkg_config_cmd = cfg->pkg_config; cfg->pkg_config = NULL;
    copt->cc_cmd = cfg->c_compiler; cfg->c_compiler = NULL;
    copt->ld_cmd = cfg->linker; cfg->linker = NULL;
    copt->cflags = cfg->cflags; cfg->cflags = NULL;
    copt->libs = cfg->libs; cfg->libs = NULL;
    copt->root_package_prefix = NULL;   // Set via cmd line
    copt->output_prefix = NULL;         // Set via cmd line, -o
    copt->search_path = cfg->package_paths; cfg->package_paths = NULL;   // Augmented via cmd line, -p
    copt->requested_modules = NULL;     // Set via cmd line, -m
    copt->do_compile = false;
    copt->do_verify = false;
    copt->cache_mode = (cfg->use_verifier_cache ? CACHE_ENABLED : CACHE_DISABLED); // Can be overridden by cmd line, --no-cache
    copt->show_progress = true;         // Set via cmd line, -q
    copt->create_debug_files = false;   // Set via cmd line, -d
    copt->continue_after_verify_error = false;    // Set via cmd line, --continue
    copt->max_child_processes = cfg->max_verifier_processes;
    copt->provers = cfg->provers; cfg->provers = NULL;
    copt->run_c_compiler = false;
    copt->print_c_compiler_commands = false;
    return copt;
}

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

// This will exit on error
static void parse_compilation_options_or_exit(int argc, char **argv,
                                              struct CompileOptions *copt,
                                              enum Subcommand cmd)
{
    enum { OPT_CONTINUE = 1, OPT_NO_CACHE = 2 };

    // Make sure to increase these sizes if adding many more options!
    struct option long_options[20];
    memset(long_options, 0, sizeof(long_options));

    char short_options[40];
    memset(short_options, 0, sizeof(short_options));

    // Add the options
    struct option *opt = long_options;
    char *optchar = short_options;

    opt->name = "root";
    opt->has_arg = required_argument;
    opt->val = 'r';
    *optchar++ = 'r'; *optchar++ = ':';
    ++opt;

    opt->name = "package-path";
    opt->has_arg = required_argument;
    opt->val = 'p';
    *optchar++ = 'p'; *optchar++ = ':';
    ++opt;

    opt->name = "output-path";
    opt->has_arg = required_argument;
    opt->val = 'o';
    *optchar++ = 'o'; *optchar++ = ':';
    ++opt;

    if (cmd == CMD_COMPILE || cmd == CMD_BUILD) {
        opt->name = "verbose";
        opt->has_arg = no_argument;
        opt->val = 'v';
        *optchar++ = 'v';
        ++opt;
    }

    if (cmd == CMD_VERIFY) {
        opt->name = "module";
        opt->has_arg = required_argument;
        opt->val = 'm';
        *optchar++ = 'm'; *optchar++ = ':';
        ++opt;
    }

    if (cmd == CMD_VERIFY || cmd == CMD_BUILD) {
        opt->name = "quiet";
        opt->has_arg = no_argument;
        opt->val = 'q';
        *optchar++ = 'q';
        ++opt;

        opt->name = "continue";
        opt->has_arg = no_argument;
        opt->val = OPT_CONTINUE;
        ++opt;

        opt->name = "timeout";
        opt->has_arg = required_argument;
        opt->val = 't';
        *optchar++ = 't'; *optchar++ = ':';
        ++opt;

        opt->name = "no-cache";
        opt->has_arg = no_argument;
        opt->val = OPT_NO_CACHE;
        ++opt;
    }

    opt->name = "debug";
    opt->has_arg = no_argument;
    opt->val = 'd';
    *optchar++ = 'd';
    ++opt;

    struct NameList **package_paths_tail = &copt->search_path;
    struct NameList **requested_modules_tail = &copt->requested_modules;

    while (true) {
        int c = getopt_long(argc, argv, short_options, long_options, NULL);

        if (c == -1) {
            break;
        }

        switch (c) {
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

static bool compilation_subcommand(int argc, char **argv,
                                   struct CompilerConfig *cfg,
                                   enum Subcommand cmd)
{
    struct CompileOptions *copt = transfer_compiler_config(cfg);

    if (cmd == CMD_TRANSLATE || cmd == CMD_COMPILE) {
        copt->do_compile = true;
    } else if (cmd == CMD_VERIFY) {
        copt->do_verify = true;
    } else {
        copt->do_compile = copt->do_verify = true;
    }

    copt->run_c_compiler = (cmd == CMD_COMPILE || cmd == CMD_BUILD);

    parse_compilation_options_or_exit(argc, argv, copt, cmd);

    bool success = compile(copt);

    if (copt->show_progress && (cmd == CMD_VERIFY || cmd == CMD_BUILD)) {
        const char *msg = (cmd == CMD_VERIFY ? "Verification" : "Build");
        if (success) {
            fprintf(stderr, "%s successful\n", msg);
        } else {
            fprintf(stderr, "%s failed\n", msg);
        }
    }

    free_compile_options(copt);
    return success;
}

//------------------------------------------------------------------------
// Main program

static void print_version()
{
    printf("bab %s\n", VERSION_STRING);
}

int main(int argc, char **argv)
{
    // Read config file.
    struct CompilerConfig *cfg = load_config_file();

    // Determine the subcommand in use.
    // This will always be in arg position 1.
    if (argc == 1 || strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0) {
        // "bab" or "bab -h" or "bab --help"
        print_general_help(stdout, argv);
        exit(0);
    } else if (strcmp(argv[1], "-V") == 0 || strcmp(argv[1], "--version") == 0) {
        // "bab -V" or "bab --version"
        print_version();
        exit(0);
    } else if (argv[1][0] == '-') {
        // "bab --something-else"
        fprintf(stderr, "Unexpected argument: %s\n", argv[1]);
        fprintf(stderr, "Try '%s --help' for help.\n", argv[0]);
        exit(1);
    }

    // At this point, argv[1] is being interpreted as a subcommand name.
    // Find out which subcommand was used.
    enum Subcommand cmd = string_to_subcommand(argv[1]);

    // Determine if '-h' or '--help' was used with a subcommand
    // (this is done here, so that we don't have to implement '--help'
    // separately in each subcommand!)
    if (cmd != CMD_UNKNOWN) {
        for (int i = 2; i < argc; ++i) {
            if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
                print_help_for_subcommand(cmd, argv, NULL);
                exit(0);
            }
        }
    }

    // Execute the subcommand.
    bool success = false;
    switch (cmd) {
    case CMD_UNKNOWN:
        // This prints the "unknown command" message
        print_help_for_subcommand(cmd, argv, argv[1]);
        break;

    case CMD_HELP:
        success = help_subcommand(argc, argv);
        break;

    case CMD_COMPILE:
    case CMD_TRANSLATE:
    case CMD_VERIFY:
    case CMD_BUILD:
        success = compilation_subcommand(argc, argv, cfg, cmd);
        break;

    case CMD_CHECK_CONFIG:
        success = check_config(cfg);
        break;

    case CMD_VERSION:
        print_version();
        success = true;
        break;
    }

    free_compiler_config(cfg);

    // Return correct exit code.
    return success ? 0 : 1;
}
