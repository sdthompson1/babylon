/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "convert_fol_to_smt.h"
#include "error.h"
#include "fol.h"
#include "run_processes.h"
#include "sexpr.h"
#include "stringbuf.h"
#include "util.h"

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

// Prover command lines (hard-coded for now)
#define NUM_PROVERS 3
#define MAX_ARGS 10
static const char * PROVERS[NUM_PROVERS][MAX_ARGS] = {
    { "z3",
      "-memory:3000",
      "-in",
      NULL },

    { "vampire",
      "--mode", "casc",
      "--memory_limit", "3000",
      "--forced_options", "output_mode=smtcomp",
      "--input_syntax", "smtlib2",
      NULL },

    { "cvc5-Linux",
      "--lang", "smt2.6",
      NULL },
};

static void print_problem(FILE *file, const struct Sexpr *problem)
{
    struct StringBuf buf;
    stringbuf_init(&buf);

    fprintf(file, "(set-logic ALL)\n");
    for (const struct Sexpr *cmd = problem; cmd; cmd = cmd->right) {
        if (cmd->type != S_PAIR) {
            fatal_error("print_problem: problem is not a proper list");
        }
        stringbuf_clear(&buf);
        format_sexpr(&buf, cmd->left);
        fprintf(file, "%s\n", buf.data);
    }

    stringbuf_free(&buf);
}

static void print_to_stdin(void *context, FILE *pipe)
{
    print_problem(pipe, context);
}

static uint64_t hash_sexpr(struct Sexpr *expr, uint64_t h)
{
    if (expr == NULL) {
        // treat this as a zero-byte
        return ((h << 5u) + h);
    }

    switch (expr->type) {
    case S_PAIR:
        // "print" the following:
        // ( left-expr space right-expr )
        h = ((h << 5u) + h) ^ (uint64_t)'(';
        h = hash_sexpr(expr->left, h);
        h = ((h << 5u) + h) ^ (uint64_t)' ';
        h = hash_sexpr(expr->right, h);
        return ((h << 5u) + h) ^ (uint64_t)')';

    case S_STRING:
        for (const char *p = expr->string; *p; ++p) {
            h = ((h << 5u) + h) ^ (uint64_t)(*p);
        }
        return h;
    }

    fatal_error("invalid sexpr");
}

static bool check_cache(const char *cache_prefix, struct Sexpr *smt_problem,
                        uint64_t *hash_out)
{
    if (cache_prefix == NULL) {
        return false;
    }

    uint64_t hash = hash_sexpr(smt_problem, 5381);
    *hash_out = hash;

    char hash_buf[17];
    sprintf(hash_buf, "%016" PRIx64, hash);

    char *filename = copy_string_2(cache_prefix, hash_buf);
    FILE *file = fopen(filename, "r");
    free(filename);

    if (file) {

        // potential cache hit. read the file to make sure.
        struct StringBuf buf;
        stringbuf_init(&buf);
        format_sexpr(&buf, smt_problem);

        bool found_difference = false;
        for (size_t i = 0; i < buf.length; ++i) {
            int c = fgetc(file);
            if (c == EOF || c != buf.data[i]) {
                found_difference = true;
                break;
            }
        }

        stringbuf_free(&buf);

        if (!found_difference) {
            // the file should end here
            if (fgetc(file) != EOF) {
                found_difference = true;
            }
        }

        fclose(file);
        return !found_difference;

    } else {
        return false;
    }
}

static void write_cache(const char *cache_prefix, struct Sexpr *smt_problem,
                        uint64_t hash)
{
    char hash_buf[17];
    sprintf(hash_buf, "%016" PRIx64, hash);

    char *filename = copy_string_2(cache_prefix, hash_buf);
    FILE *file = fopen(filename, "w");
    free(filename);

    if (file) {
        struct StringBuf buf;
        stringbuf_init(&buf);
        format_sexpr(&buf, smt_problem);
        fwrite(buf.data, buf.length, 1, file);
        stringbuf_free(&buf);
        fclose(file);
    }
}

static bool is_sat(const char *output, int output_length)
{
    return output_length >= 3 && memcmp(output, "sat", 3) == 0;
}

static bool is_unsat(const char *output, int output_length)
{
    return output_length >= 5 && memcmp(output, "unsat", 5) == 0;
}

static bool is_unknown(const char *output, int output_length)
{
    return output_length >= 7 && memcmp(output, "unknown", 7) == 0;
}

static bool should_stop(void *context, const char *output, int output_length)
{
    return is_sat(output, output_length) || is_unsat(output, output_length);
}

static enum FolResult interpret_result(struct Job *job,
                                       bool print_progress_messages,
                                       struct Process *proc)
{
    if (is_unsat(proc->output, proc->output_length)) {
        if (print_progress_messages) {
            fprintf(stderr, "(%s, %.1fs)\n", proc->cmd[0], job->time_in_seconds);
        }
        return FOL_RESULT_PROVED;
    } else if (is_sat(proc->output, proc->output_length)) {
        if (print_progress_messages) {
            fprintf(stderr, "(%s returned 'sat')\n", proc->cmd[0]);
        }
        return FOL_RESULT_DISPROVED;
    } else if (is_unknown(proc->output, proc->output_length) || proc->output_length == 0) {
        // (sometimes vampire gives empty results, we treat that the same as "unknown")
        return FOL_RESULT_UNKNOWN;
    } else {
        if (!proc->interrupted) {
            // nul-terminate the output
            if (proc->output_length < MAX_OUTPUT) {
                proc->output[proc->output_length] = 0;
            } else {
                proc->output[MAX_OUTPUT - 1] = 0;
            }

            fprintf(stderr, "\nWARNING: unexpected output from prover [%s]: %s\n",
                    proc->cmd[0], proc->output);
        }
        return FOL_RESULT_UNKNOWN;
    }
}

static enum FolResult solve_smt_problem(struct Sexpr *smt_problem,
                                        bool print_progress_messages,
                                        int timeout_seconds)
{
    struct Job job;
    job.procs = alloc(sizeof(struct Process) * NUM_PROVERS);
    job.num_procs = NUM_PROVERS;
    job.timeout_in_seconds = timeout_seconds;
    job.print_timeout_message = print_progress_messages;
    job.print_to_stdin = print_to_stdin;
    job.should_stop = should_stop;
    job.context = smt_problem;

    for (int i = 0; i < NUM_PROVERS; ++i) {
        job.procs[i].cmd = PROVERS[i];
    }

    run_processes(&job);

    enum FolResult result = FOL_RESULT_UNKNOWN;

    for (int i = 0; i < NUM_PROVERS; ++i) {
        enum FolResult new_result = interpret_result(&job, print_progress_messages, &job.procs[i]);
        if (new_result != FOL_RESULT_UNKNOWN){

            if (result == FOL_RESULT_UNKNOWN) {
                result = new_result;
            } else if (result != new_result) {
                fatal_error("solvers gave inconsistent results");
            }

        }
    }

    if (result == FOL_RESULT_UNKNOWN && !job.timeout && print_progress_messages) {
        fprintf(stderr, "('unknown', %.1fs)\n", job.time_in_seconds);
    }

    free(job.procs);

    return result;
}

enum FolResult solve_fol_problem(struct Sexpr *fol_problem,
                                 const char *cache_prefix,
                                 const char *debug_filename,
                                 bool print_progress_messages,
                                 int timeout_seconds)
{
    if (debug_filename) {
        char *fol_filename = copy_string_2(debug_filename, ".fol");
        FILE *file = fopen(fol_filename, "w");
        free(fol_filename);
        if (file) {
            print_problem(file, fol_problem);
            fclose(file);
        }
    }

    // convert it from FOL to SMT
    struct Sexpr *smt_problem = convert_fol_to_smt(fol_problem);

    if (debug_filename) {
        char *smt_filename = copy_string_2(debug_filename, ".smt");
        FILE *file = fopen(smt_filename, "w");
        free(smt_filename);
        if (file) {
            print_problem(file, smt_problem);
            fclose(file);
        }
    }

    // check the cache
    uint64_t hash;
    bool cache_hit = check_cache(cache_prefix, smt_problem, &hash);
    if (cache_hit) {
        if (print_progress_messages) {
            fprintf(stderr, "(cached)\n");
        }
        return FOL_RESULT_PROVED;
    }

    // call the external solvers
    enum FolResult result = solve_smt_problem(smt_problem, print_progress_messages, timeout_seconds);

    // successful results can be written back to the cache
    if (result == FOL_RESULT_PROVED) {
        write_cache(cache_prefix, smt_problem, hash);
    }

    free_sexpr(smt_problem);

    return result;
}
