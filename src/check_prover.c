/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "alloc.h"
#include "check_prover.h"
#include "config_file.h"
#include "error.h"
#include "process.h"
#include "util.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static bool match_string(const char *buf, int buf_len,
                         const char *str, int str_len)
{
    // We only check the beginning of 'buf' for a match - i.e. there can
    // be garbage afterwards.
    // We also skip any whitespace at the beginning of 'buf'.
    int i = 0;
    while (i < buf_len && isspace(buf[i])) ++i;
    return (i + str_len <= buf_len && memcmp(&buf[i], str, str_len) == 0);
}

bool is_unsat(const char *buf, int len)
{
    return match_string(buf, len, "unsat", 5);
}

bool is_sat(const char *buf, int len)
{
    return match_string(buf, len, "sat", 3);
}

bool is_unknown(const char *buf, int len)
{
    return match_string(buf, len, "unknown", 7);
}


static void print_test_job(void *context, FILE *pipe)
{
    // We will ask the prover to prove "x=x". It should return "unsat".
    fprintf(pipe, "(set-logic ALL)\n");
    fprintf(pipe, "(declare-const x Int)\n");
    fprintf(pipe, "(assert (not (= x x)))\n");
    fprintf(pipe, "(check-sat)\n");
}

static void run_test_job(const char **cmd,
                         struct Process *proc,
                         bool show_stderr,
                         bool show_exec_errors)
{
    default_init_process(proc);
    proc->cmd = cmd;
    proc->print_to_stdin = print_test_job;
    proc->context = NULL;
    proc->show_stderr = show_stderr;
    proc->show_exec_errors = show_exec_errors;

    launch_process(proc);
    while (proc->status == PROC_RUNNING) update_processes(true);
}

static bool test_job_successful(struct Process *proc)
{
    if (proc->status != PROC_SUCCESS) return false;
    return is_unsat(proc->output, proc->output_length);
}

bool check_prover(struct ProverConfig *pr)
{
    if (pr->format != FORMAT_SMTLIB) fatal_error("unsupported prover format");

    printf(" - Checking prover [%s]\n", pr->name);

    struct Process proc;
    run_test_job(pr->command_and_arguments, &proc, pr->show_stderr, true);

    if (test_job_successful(&proc)) {
        return true;
    } else if (proc.status != PROC_SUCCESS) {
        return false;
    } else {
        if (proc.output_length < MAX_OUTPUT) {
            proc.output[proc.output_length] = 0;
        } else {
            proc.output[MAX_OUTPUT - 1] = 0;
        }
        printf("Command [%s] returned unexpected output:\n%s\n",
               pr->command_and_arguments[0], proc.output);
        return false;
    }
}

// Returns static string
const char * standard_prover_name(enum StandardProver prover)
{
    switch (prover) {
    case PROVER_Z3: return "z3";
    case PROVER_CVC4: return "cvc4";
    case PROVER_CVC5: return "cvc5";
    case PROVER_VAMPIRE: return "vampire";
    case PROVER_ALT_ERGO: return "alt-ergo";
    case NUM_STD_PROVERS: break;
    }

    fatal_error("bad StandardProver value");
}

#define MAX_CMD 10

// Returns true if array filled, or false if "n" is too large.
static bool standard_prover_command(enum StandardProver prover, int n, const char * cmd[MAX_CMD])
{
    switch (prover) {
    case PROVER_Z3:
        if (n == 0) {
            cmd[0] = "z3";
            cmd[1] = "-in";
            cmd[2] = NULL;
            return true;
        } else {
            return false;
        }

    case PROVER_CVC4:
        if (n == 0) {
            cmd[0] = "cvc4";
            cmd[1] = "--lang";
            cmd[2] = "smt2.6";
            cmd[3] = NULL;
            return true;
        } else {
            return false;
        }

    case PROVER_CVC5:
        // Downloading cvc5 for Linux from https://github.com/cvc5/cvc5/releases/ gives
        // you a binary called "cvc5" for versions 1.1.1 onwards, but before that, it
        // gave you a binary called "cvc5-Linux". We will look for both.
        if (n == 0) {
            cmd[0] = "cvc5";
        } else if (n == 1) {
            cmd[0] = "cvc5-Linux";
        } else {
            return false;
        }
        cmd[1] = "--lang";
        cmd[2] = "smt2.6";
        cmd[3] = NULL;
        return true;

    case PROVER_VAMPIRE:
        if (n == 0) {
            cmd[0] = "vampire";
            cmd[1] = "--forced_options";
            cmd[2] = "output_mode=smtcomp";
            cmd[3] = "--input_syntax";
            cmd[4] = "smtlib2";
            cmd[5] = NULL;
            return true;
        } else {
            return false;
        }

    case PROVER_ALT_ERGO:
        if (n == 0) {
            cmd[0] = "alt-ergo";
            cmd[1] = NULL;
            return true;
        } else {
            return false;
        }

    case NUM_STD_PROVERS:
        break;
    }

    fatal_error("bad StandardProver value");
}

static char * additional_prover_config(enum StandardProver prover)
{
    switch (prover) {
    case PROVER_Z3:
        return copy_string("");

    case PROVER_CVC4:
        return copy_string("signal = \"SIGHUP\"     # cvc4 is slow to respond to SIGTERM; use SIGHUP instead\n");

    case PROVER_CVC5:
        return copy_string("show-stderr = false   # Suppress unwanted \"cvc5 interrupted by SIGTERM\" messages\n");

    case PROVER_VAMPIRE:
        return copy_string("signal = \"SIGINT\"             # Vampire doesn't seem to respond to SIGTERM; use SIGINT instead\n"
                           "show-stderr = false           # Suppress unwanted vampire debug output\n"
                           "ignore-empty-output = true    # Vampire sometimes doesn't print any output; ignore this\n"
                           "ignore-exit-status = true     # Vampire sometimes returns with non-zero exit status; ignore this\n");

    case PROVER_ALT_ERGO:
        return copy_string("show-stderr = false   # Suppress unwanted alt-ergo debug output\n");

    case NUM_STD_PROVERS:
        break;
    }

    fatal_error("bad StandardProver value");
}

static char * comment_out(const char *str)
{
    int num_lines = 1;
    int len = 0;
    for (const char *p = str; *p; ++p) {
        if (*p == '\n') {
            ++num_lines;
        }
        ++len;
    }

    char *result = alloc(len + num_lines*2 + 1);
    result[0] = '#';
    result[1] = ' ';

    const char *from = str;
    char *to = result + 2;

    while (*from && to < result + len + num_lines*2) {
        *to = *from;
        if (*from == '\n' && from[1] != 0) {
            ++to;
            *to = '#';
            ++to;
            *to = ' ';
        }
        ++from;
        ++to;
    }

    *to = 0;  // null terminate the string

    return result;
}

bool detect_standard_prover(enum StandardProver prover, char **config)
{
    const char * cmd[MAX_CMD];
    bool ok = false;
    int n = 0;

    while (true) {
        bool found = standard_prover_command(prover, n, cmd);
        if (!found) break;

        struct Process proc;
        run_test_job(cmd, &proc, false, false);  // silence all output for the auto-detection

        if (test_job_successful(&proc)) {
            ok = true;
            break;
        }

        ++n;
    }

    if (!ok) {
        // None of the prover command lines worked for this prover.
        // Revert back to the n=0 command-line for config purposes.
        standard_prover_command(prover, 0, cmd);
    }

    // Build config string.
    char *str1 = copy_string_3("[provers.", standard_prover_name(prover), "]\n");
    char *str2 = copy_string_3("command = \"", cmd[0], "\"\n");
    char *str3 = copy_string("arguments = [");
    for (const char **arg = &cmd[1]; *arg; ++arg) {
        char *str = copy_string_5(str3, arg==&cmd[1] ? "" : ", ", "\"", *arg, "\"");
        free(str3);
        str3 = str;
    }
    char *str4 = copy_string_3("]\n",
                               "format = \"smtlib\"\n",
                               "timeout = 60          # In seconds\n");
    char *str5 = additional_prover_config(prover);

    char *result = copy_string_5(str1, str2, str3, str4, str5);
    free(str1);
    free(str2);
    free(str3);
    free(str4);
    free(str5);

    if (ok) {
        *config = result;
        return true;
    } else {
        *config = copy_string_4("## Uncomment the following to use ",
                                standard_prover_name(prover),
                                ":\n",
                                comment_out(result));
        free(result);
        return false;
    }
}
