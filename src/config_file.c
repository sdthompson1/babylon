/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#define _GNU_SOURCE    // for NSIG

#include "alloc.h"
#include "check_prover.h"
#include "config_file.h"
#include "error.h"
#include "make_dir.h"
#include "toml_ext.h"

#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>


#define CONFIG_DIR_NAME "babylon"
#define CONFIG_FILE_NAME "babylon.toml"

#define DEFAULT_CC "gcc"
#define DEFAULT_LD "gcc"
#define DEFAULT_PKG_CONFIG "pkg-config"

// Get "base" dir for config -- usually "$HOME/.config".
// Returns allocated string. Never returns NULL.
static char * get_config_base()
{
    // XDG spec says to use $XDG_CONFIG_HOME, or $HOME/.config
    // if that is undefined.

    char *dir = getenv("XDG_CONFIG_HOME");
    if (dir != NULL) {
        return copy_string(dir);
    }

    dir = getenv("HOME");
    if (dir == NULL) {
        // In this case we do not know where the config file should go, so
        // we just give up and exit.
        fprintf(stderr, "Error: HOME environment variable is not defined.\n");
        exit(1);
    }

    return copy_string_2(dir, "/.config");
}

// Make the base_dir/babylon directory, or exit process on failure.
static void make_config_dir_if_required(char *base_dir)
{
    const char *dir = copy_string_2(base_dir, "/" CONFIG_DIR_NAME);
    if (!maybe_mkdir(dir, 0777)) {
        fprintf(stderr, "## Failed to create config directory: %s\n", dir);
        exit(1);
    }
}

// Suggest some [provers] text to add to the config file.
// Returns an allocated string.
static char * suggest_prover_config()
{
    char * provers_text = NULL;
    char * config_text = NULL;

    for (int i = 0; i < NUM_STD_PROVERS; ++i) {
        char *cfg_txt;
        bool ok = detect_standard_prover(i, &cfg_txt);

        if (ok) {
            if (provers_text == NULL) {
                provers_text = copy_string(standard_prover_name(i));
            } else {
                char *str = copy_string_3(provers_text, ", ", standard_prover_name(i));
                free(provers_text);
                provers_text = str;
            }
        }

        if (config_text == NULL) {
            config_text = cfg_txt;
        } else {
            char *str = copy_string_3(config_text, "\n", cfg_txt);
            free(config_text);
            free(cfg_txt);
            config_text = str;
        }
    }

    if (provers_text) {
        fprintf(stderr, "## The following provers were detected and configured: [%s].\n", provers_text);
        free(provers_text);
    } else {
        fprintf(stderr,
                "## WARNING: No provers were detected on this system. Please install one or\n"
                "## more SMT solvers and/or edit the config file manually.\n");
    }

    return config_text;
}

// Create a default config at 'filename', or exit process on failure.
static void create_default_config_file(char *filename)
{
    FILE *file = fopen(filename, "w");
    if (file == NULL) {
        fprintf(stderr, "## Creating config file failed!\n");
        exit(1);
    }

    char *prover_config_text = suggest_prover_config();

    const char *BASE_CONFIG_TEXT =
        "# Config file for the Babylon compiler.\n"
        "\n"
        "[packages]\n"
        "paths = []            # Local directories to search for Babylon packages\n"
        "\n"
        "[c-compiler]\n"
        "cc = \"gcc\"                  # C compiler command\n"
        "ld = \"gcc\"                  # Linker command\n"
        "pkg-config = \"pkg-config\"   # pkg-config command\n"
        "cflags = [\"-g\"]             # C compiler additional arguments\n"
        "libs = []                   # Linker additional arguments\n"
        "\n"
        "[verifier]\n"
        "use-cache = true      # Whether to use the verifier cache\n"
        "max-processes = 0     # Number of worker processes. 0 means to guess automatically\n"
        "                      # based on available CPU cores and memory.\n"
        "\n";

    int put1 = fputs(BASE_CONFIG_TEXT, file);
    int put2 = fputs(prover_config_text, file);
    int cl = fclose(file);

    free(prover_config_text);

    if (put1 == EOF || put2 == EOF || cl == EOF) {
        fprintf(stderr, "Error creating default config file at %s.\n", filename);
        exit(1);
    }
}

static void set_max_verifier_processes(struct CompilerConfig *cfg)
{
    if (cfg->max_verifier_processes >= 1) {
        // A valid value is already set; don't overwrite it.
        return;
    }

    // Guess an appropriate number of worker processes, based on the
    // following heuristics:
    //  - Don't run more processes than we have online CPU cores.
    //  - Don't run more processes than we have gigabytes of physical
    //    RAM installed.

    // Use sysconf to get the required information.

    long num_cpu = sysconf(_SC_NPROCESSORS_ONLN);
    long page_size_in_bytes = sysconf(_SC_PAGESIZE);
    long num_physical_pages = sysconf(_SC_PHYS_PAGES);   // Linux specific?

    // check for errors
    if (num_cpu < 1 || page_size_in_bytes < 1 || num_physical_pages < 1) {
        fprintf(stderr, "Error: sysconf call failed\n");
        exit(1);
    }

    uint64_t bytes = ((uint64_t)page_size_in_bytes) * ((uint64_t)num_physical_pages);

    // Convert bytes to gigabytes, rounding to nearest integer (roughly)
    uint64_t one_gigabyte = UINT64_C(1024) * UINT64_C(1024) * UINT64_C(1024);
    uint64_t gigabytes = (bytes + one_gigabyte/2) / one_gigabyte;
    if (gigabytes < 1) gigabytes = 1;

    // Limit to num CPUs or num gigabytes physical RAM, whichever is lower.
    uint64_t minimum = (uint64_t)num_cpu < gigabytes ? (uint64_t)num_cpu : gigabytes;

    // Set result
    cfg->max_verifier_processes = minimum;
}

// Look for a list-of-strings under a given key in the given table.
// If the key is not present, defaults to [].
// If the key is present but has wrong type, this exits the process.
static struct NameList *read_list_of_strings(const char *filename,
                                             toml_table_t *table,
                                             const char *key)
{
    bool err = false;
    toml_array_t *array = toml_table_array_ext(filename, table, key, &err);
    if (err) exit(1);

    if (array == NULL) {
        return NULL;
    } else {
        struct NameList *result = read_toml_string_list(filename, array, &err);
        if (err) exit(1);
        return result;
    }
}

// Parse the [packages] section
static void parse_packages(const char *filename,
                           toml_table_t *main_table,
                           struct CompilerConfig *cfg)
{
    toml_table_t *packages_table = toml_table_table(main_table, "packages");
    if (packages_table != NULL) {
        cfg->package_paths = read_list_of_strings(filename, packages_table, "paths"); // Default []
    }
}

// Parse the [c-compiler] section
static void parse_c_compiler(const char *filename,
                             toml_table_t *main_table,
                             struct CompilerConfig *cfg)
{
    toml_table_t *c_compiler_table = toml_table_table(main_table, "c-compiler");
    if (c_compiler_table == NULL) {
        // Ensure defaults are set correctly in this case
        cfg->c_compiler = copy_string(DEFAULT_CC);
        cfg->linker = copy_string(DEFAULT_LD);
        cfg->pkg_config = copy_string(DEFAULT_PKG_CONFIG);
    } else {
        cfg->c_compiler = read_toml_string(filename, c_compiler_table, "cc", DEFAULT_CC);
        cfg->linker = read_toml_string(filename, c_compiler_table, "ld", DEFAULT_LD);
        cfg->cflags = read_list_of_strings(filename, c_compiler_table, "cflags"); // Default []
        cfg->libs = read_list_of_strings(filename, c_compiler_table, "libs"); // Default []
        cfg->pkg_config = read_toml_string(filename, c_compiler_table, "pkg-config", DEFAULT_PKG_CONFIG);
    }
}

// Parse the [verifier] section
static void parse_verifier(const char *filename,
                           toml_table_t *main_table,
                           struct CompilerConfig *cfg)
{
    toml_table_t *verifier_table = toml_table_table(main_table, "verifier");
    if (verifier_table == NULL) {
        // Ensure defaults are set correctly in this case
        cfg->use_verifier_cache = true;
    } else {
        toml_value_t val = toml_table_bool(verifier_table, "use-cache");
        cfg->use_verifier_cache = val.ok ? val.u.b : true;   // Default true

        val = toml_table_int(verifier_table, "max-processes");
        cfg->max_verifier_processes = val.ok ? val.u.i : 0;  // Default 0
    }
}

// Convert a signal name to a signal number.
// This might be non-portable (e.g. it needs NSIG and sigabbrev_np, and
// assumes signal numbers are sequential from 1).
// Returns 0 if the name is not found.
static int sig_name_to_num(const char *name)
{
    for (int i = 1; i < NSIG; ++i) {
        const char *abbrev = sigabbrev_np(i);
        if (abbrev != NULL) {
            if (strcmp(abbrev, name) == 0) {
                return i;
            }
            char *sigabbr = copy_string_2("SIG", abbrev);
            if (strcmp(sigabbr, name) == 0) {
                free(sigabbr);
                return i;
            }
            free(sigabbr);
        }
    }
    return 0;
}

static const char **make_cmd_array(char *cmd, struct NameList *args)
{
    // Need one array entry per argument, plus 2 more (for command
    // name and the final NULL).
    const char **arr = alloc(sizeof(char*) * (2 + name_list_length(args)));
    arr[0] = cmd;  // transfer ownership

    int i = 1;
    for (struct NameList *node = args; node; node = node->next, ++i) {
        arr[i] = node->name;
        node->name = NULL;
    }

    arr[i] = NULL;

    free_name_list(args);

    return arr;
}

// Parse one [prover.XXX] section
static void parse_prover(const char *filename,
                         toml_table_t *provers_table,
                         const char *key,
                         struct ProverConfig ***tail)
{
    toml_table_t *table = toml_table_table(provers_table, key);

    struct ProverConfig *cfg = alloc(sizeof(struct ProverConfig));
    cfg->next = NULL;

    cfg->name = copy_string(key);

    char *command = read_toml_string(filename, table, "command", NULL);
    if (command == NULL) exit(1);

    struct NameList *arguments = read_list_of_strings(filename, table, "arguments");  // Default []

    // this next call frees command and arguments
    cfg->command_and_arguments = make_cmd_array(command, arguments);

    char *fmt_str = read_toml_string(filename, table, "format", "smtlib");
    if (strcmp(fmt_str, "smtlib") == 0) {
        cfg->format = FORMAT_SMTLIB;
    } else if (strcmp(fmt_str, "tptp") == 0) {
        cfg->format = FORMAT_TPTP;
    } else {
        fprintf(stderr, "%s: Invalid value for 'format': '%s'\n", filename, fmt_str);
        exit(1);
    }
    free(fmt_str);

    toml_value_t val = toml_table_bool(table, "show-stderr");
    cfg->show_stderr = val.ok ? val.u.b : true;  // Default true

    val = toml_table_bool(table, "ignore-exit-status");
    cfg->ignore_exit_status = val.ok ? val.u.b : false;   // Default false

    val = toml_table_bool(table, "ignore-empty-output");
    cfg->ignore_empty_output = val.ok ? val.u.b : false;  // Default false

    val = toml_table_int(table, "timeout");
    cfg->timeout = val.ok ? val.u.i : 60;  // Default 60

    val = toml_table_int(table, "signal");
    if (val.ok) {
        cfg->signal = val.u.i;
    } else {
        val = toml_table_string(table, "signal");
        if (val.ok) {
            int sig = sig_name_to_num(val.u.s);
            if (sig == 0) {
                fprintf(stderr, "%s: Unknown signal name: %s\n", filename, val.u.s);
                exit(1);
            }
            free(val.u.s);
            cfg->signal = sig;
        } else {
            // 'signal' not present, or not recognized as string nor integer.
            // Default to SIGTERM.
            cfg->signal = SIGTERM;
        }
    }

    val = toml_table_int(table, "kill-timeout");
    cfg->kill_timeout = val.ok ? val.u.i : 10;  // Default 10

    **tail = cfg;
    *tail = &cfg->next;
}

// Parse the [provers] section
static void parse_provers(const char *filename,
                          toml_table_t *main_table,
                          struct CompilerConfig *cfg)
{
    toml_table_t *table = toml_table_table(main_table, "provers");
    if (table != NULL) {
        int n = toml_table_len(table);
        struct ProverConfig **tail = &cfg->provers;
        for (int i = 0; i < n; ++i) {
            int keylen;
            parse_prover(filename, table, toml_table_key(table, i, &keylen), &tail);
        }
    }
}

// this takes ownership of 'filename'
static struct CompilerConfig * parse_compiler_config(const char *filename, toml_table_t *main_table)
{
    struct CompilerConfig *cfg = alloc(sizeof(struct CompilerConfig));
    memset(cfg, 0, sizeof(*cfg));

    cfg->config_filename = filename;

    parse_packages(filename, main_table, cfg);
    parse_c_compiler(filename, main_table, cfg);
    parse_verifier(filename, main_table, cfg);
    parse_provers(filename, main_table, cfg);

    set_max_verifier_processes(cfg);

    return cfg;
}

// Load the config file (creating a default if necessary).
struct CompilerConfig * load_config_file()
{
    char *base_dir = get_config_base();
    char *filename = copy_string_2(base_dir, "/" CONFIG_DIR_NAME "/" CONFIG_FILE_NAME);

    FILE *file = fopen(filename, "r");

    if (file == NULL && errno == ENOENT) {
        // Config file doesn't exist; create a default config file
        // (or exit process!).
        fprintf(stderr, "## Config file [%s] does not exist; creating it.\n", filename);
        make_config_dir_if_required(base_dir);
        create_default_config_file(filename);

        // Reopen the file now that it has been created.
        file = fopen(filename, "r");
    }

    if (file == NULL) {
        // If the config couldn't be opened, that is a fatal error.
        fprintf(stderr, "Error: Failed to read config file: %s\n", filename);
        exit(1);
    }

    char errbuf[200];
    toml_table_t *main_table = toml_parse_file(file, errbuf, sizeof(errbuf));
    if (!main_table) {
        fprintf(stderr, "Error while parsing %s: %s\n", filename, errbuf);
        exit(1);
    }

    struct CompilerConfig *cfg = parse_compiler_config(filename, main_table);

    toml_free(main_table);
    fclose(file);
    free(base_dir);

    return cfg;
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

void free_prover_config(struct ProverConfig *p)
{
    while (p) {
        struct ProverConfig *next = p->next;
        free((char*)p->name);
        free_string_array(p->command_and_arguments);
        free(p);
        p = next;
    }
}

void free_compiler_config(struct CompilerConfig *cfg)
{
    free((char*)cfg->config_filename);
    free_name_list(cfg->package_paths);
    free((char*)cfg->c_compiler);
    free((char*)cfg->linker);
    free_name_list(cfg->cflags);
    free_name_list(cfg->libs);
    free((char*)cfg->pkg_config);
    free_prover_config(cfg->provers);
    free(cfg);
}
