/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "cache_db.h"
#include "convert_fol_to_smt.h"
#include "error.h"
#include "fol.h"
#include "run_processes.h"
#include "sexpr.h"
#include "sha256.h"
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

static void hash_sexpr(struct Sexpr *expr, struct SHA256_CTX *ctx)
{
    if (expr == NULL) {
        sha256_add_byte(ctx, 1);
        return;
    }

    switch (expr->type) {
    case S_PAIR:
        sha256_add_byte(ctx, 2);
        hash_sexpr(expr->left, ctx);
        hash_sexpr(expr->right, ctx);
        return;

    case S_STRING:
        sha256_add_byte(ctx, 3);
        sha256_add_bytes(ctx, (const uint8_t*)expr->string, strlen(expr->string) + 1);
        return;
    }

    fatal_error("invalid sexpr");
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
            fprintf(stderr, "(%s, %.1fs)", proc->cmd[0], job->time_in_seconds);
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

            fprintf(stderr, "\n\nWARNING: unexpected output from prover [%s]: %s\n",
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
        if (new_result != FOL_RESULT_UNKNOWN) {
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

    if (result != FOL_RESULT_UNKNOWN && print_progress_messages) {
        fprintf(stderr, "\n");
    }

    free(job.procs);

    return result;
}

enum FolResult solve_fol_problem(struct Sexpr *fol_problem,
                                 struct CacheDb *cache_db,
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
    uint8_t hash[SHA256_HASH_LENGTH];
    if (cache_db) {
        struct SHA256_CTX ctx;
        sha256_init(&ctx);
        sha256_add_bytes(&ctx, (const uint8_t*)"SMT", 4);
        hash_sexpr(smt_problem, &ctx);
        sha256_final(&ctx, hash);
    }

    if (sha256_exists_in_db(cache_db, SMT_QUERY_HASH, hash)) {
        free_sexpr(smt_problem);
        if (print_progress_messages) {
            fprintf(stderr, "(cached)\n");
        }
        return FOL_RESULT_PROVED;
    }

    // call the external solvers
    enum FolResult result = solve_smt_problem(smt_problem, print_progress_messages, timeout_seconds);

    // successful results can be written back to the cache
    if (result == FOL_RESULT_PROVED) {
        add_sha256_to_db(cache_db, SMT_QUERY_HASH, hash);
    }

    free_sexpr(smt_problem);

    return result;
}
