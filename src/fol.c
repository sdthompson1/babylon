/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "convert_fol_to_smt.h"
#include "error.h"
#include "fol.h"
#include "process.h"
#include "sexpr.h"
#include "sha256.h"
#include "stringbuf.h"
#include "util.h"

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

// Prover command lines (hard-coded for now).
// TODO: This should be loaded from a config file, or some such.
// TODO: If any prover in the list fails to start, we should print some sort of warning/error
// message to stderr. (Currently this only happens if ALL provers fail to start.)
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
      NULL }
};

// Max number of simultaneous child processes -- adjust to suit your
// machine.
// It works best if this value is at least equal to NUM_PROVERS, and
// preferably higher -- but make sure you have enough RAM for your
// chosen number of processes.
#define MAX_PROVER_PROCESSES 3

// Max number of SMT jobs that can be queueing up waiting to run.
// There probably isn't much need to tune this, the default should work fine.
#define MAX_JOB_QUEUE_LENGTH (((MAX_PROVER_PROCESSES / NUM_PROVERS) * 200) + 20)


// Job and FolRunner structs.
struct Job {
    struct Job *next;

    // Child processess (see process.h)
    struct Process procs[NUM_PROVERS];
    int num_started;

    // When the job comes to the head of the list, the announce_msg is printed.
    const char *announce_msg;   // allocated

    // This is initially NULL, but when the job is complete, this is set to an
    // appropriate message (e.g. "(z3, 1.0s)"). It will be printed when the job
    // comes to the head of the list with active==false.
    const char *completion_msg; // allocated

    // This is initially set to a suitable error message, but will be
    // cleared to NULL if the job completes without error. It is
    // printed when the job reaches the head of the list with
    // active==false.
    const char *error_msg;      // allocated

    // Storage for the SMT problem itself. This can be freed once all
    // child processes have been started.
    struct Sexpr *smt_problem;          // allocated
    uint8_t hash[SHA256_HASH_LENGTH];   // hash of smt_problem

    // Whether to show progress messages. This can now be set per-job.
    bool show_progress;

    // active==true means the job is either not started yet, or in
    // progress. active==false means the job has completed (or didn't
    // need to run in the first place, e.g. a cache hit, or a "fake"
    // job created by add_fol_message).
    bool active;

    // This is set to true if the job has raised a verifier error
    // (e.g. 'sat' or 'unknown' result, or timeout).
    bool error_flag;

    // If add_to_cache_db is true, then when the job reaches the head
    // of the list (with active==false), the hash_to_be_added will be
    // added to the DB -- but only if no errors were reached before
    // that point.
    bool add_to_cache_db;
    enum HashType hash_type;
    uint8_t hash_to_be_added[SHA256_HASH_LENGTH];
};

struct FolRunner {
    // Job Queue
    struct Job *jobs_head;    // points to first job in list
    struct Job **jobs_tail;   // points to 'next' pointer of last job, or to jobs_head
    int num_jobs;             // length of list

    // Error Flags
    // Note difference between error_found and error_reached!
    bool error_found;         // true if any job has failed
    bool error_reached;       // true if an error-job has reached the head of the list

    // Configuration
    struct CacheDb *cache_db;
    int timeout_seconds;
    bool continue_after_error;
};

// We keep a global FolRunner object.
struct FolRunner * g_fol_runner;


void start_fol_runner(struct CacheDb *cache_db,
                      int timeout_seconds,
                      bool continue_after_error)
{
    if (g_fol_runner) {
        fatal_error("fol runner already started");
    }
    g_fol_runner = alloc(sizeof(struct FolRunner));
    g_fol_runner->jobs_head = NULL;
    g_fol_runner->jobs_tail = &g_fol_runner->jobs_head;
    g_fol_runner->num_jobs = 0;
    g_fol_runner->error_found = false;
    g_fol_runner->error_reached = false;
    g_fol_runner->cache_db = cache_db;
    g_fol_runner->timeout_seconds = timeout_seconds;
    g_fol_runner->continue_after_error = continue_after_error;
}

static void free_job(struct Job *job)
{
    free((char*)job->announce_msg);
    free((char*)job->completion_msg);
    free((char*)job->error_msg);
    free_sexpr(job->smt_problem);
    free(job);
}

void stop_fol_runner()
{
    if (!g_fol_runner) {
        fatal_error("fol runner not started");
    }
    wait_fol_complete();
    while (g_fol_runner->jobs_head) {
        struct Job *next = g_fol_runner->jobs_head->next;
        free_job(g_fol_runner->jobs_head);
        g_fol_runner->jobs_head = next;
    }
    free(g_fol_runner);
}

bool fol_continue_after_error()
{
    return g_fol_runner->continue_after_error;
}

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
    // Note that sometimes vampire returns empty results -- we treat
    // that the same as "unknown".
    return (output_length >= 7 && memcmp(output, "unknown", 7) == 0)
        || output_length == 0;
}

void solve_fol_problem(struct Sexpr *fol_problem,   // handover
                       bool show_progress,
                       const char *announce_msg,    // handover
                       const char *error_msg,       // handover
                       const char *debug_filename)
{
    // Block until the queue has gone down to a reasonable size (if required).
    while (g_fol_runner->num_jobs > MAX_JOB_QUEUE_LENGTH) {
        update_processes(true);
        update_fol_status();
    }

    // Save .fol file for debugging if required.
    if (debug_filename) {
        char *fol_filename = copy_string_2(debug_filename, ".fol");
        FILE *file = fopen(fol_filename, "w");
        free(fol_filename);
        if (file) {
            print_problem(file, fol_problem);
            fclose(file);
        }
    }

    // Convert from FOL to SMT.
    struct Sexpr *smt_problem = convert_fol_to_smt(fol_problem);
    fol_problem = NULL;

    // Save .smt file for debugging if required.
    if (debug_filename) {
        char *smt_filename = copy_string_2(debug_filename, ".smt");
        FILE *file = fopen(smt_filename, "w");
        free(smt_filename);
        if (file) {
            print_problem(file, smt_problem);
            fclose(file);
        }
    }

    // Create a new Job.
    struct Job *job = alloc(sizeof(struct Job));

    job->next = NULL;

    for (int i = 0; i < NUM_PROVERS; ++i) {
        job->procs[i].cmd = PROVERS[i];
        job->procs[i].print_to_stdin = print_to_stdin;
        job->procs[i].context = smt_problem;
        job->procs[i].timeout_in_seconds = g_fol_runner->timeout_seconds;
    }

    job->num_started = 0;

    job->announce_msg = announce_msg;
    job->completion_msg = NULL;
    job->error_msg = error_msg;
    job->smt_problem = smt_problem;
    job->active = true;
    job->error_flag = false;

    job->add_to_cache_db = false;

    job->show_progress = show_progress;

    // Check the cache.
    if (g_fol_runner->cache_db) {
        struct SHA256_CTX ctx;
        sha256_init(&ctx);
        sha256_add_bytes(&ctx, (const uint8_t*)"SMT", 4);
        hash_sexpr(smt_problem, &ctx);
        sha256_final(&ctx, job->hash);

        if (sha256_exists_in_db(g_fol_runner->cache_db, SMT_QUERY_HASH, job->hash)) {
            // We can "complete" the job immediately.
            job->active = false;
            free_sexpr(job->smt_problem);
            job->smt_problem = NULL;
            job->completion_msg = copy_string(" (cached)\n");
            free((char*)job->error_msg);
            job->error_msg = NULL;
        }
    }

    // Add the job to the list.
    *(g_fol_runner->jobs_tail) = job;
    g_fol_runner->jobs_tail = &(job->next);
    ++(g_fol_runner->num_jobs);

    // Update status. This will launch the new job if appropriate.
    update_fol_status();
}

void add_fol_message(const char *msg,   // handover
                     bool is_error,
                     enum HashType hash_type,
                     const uint8_t *hash)
{
    // Add a "dummy" job, which has active==false (so it won't launch
    // any child processes), but which has an announce_msg or
    // error_msg (so the msg will be printed when this job reaches the
    // head of the queue).

    struct Job *job = alloc(sizeof(struct Job));

    job->next = NULL;
    job->num_started = 0;
    job->announce_msg = is_error ? NULL : msg;
    job->completion_msg = NULL;
    job->error_msg = is_error ? msg : NULL;
    job->smt_problem = NULL;
    job->active = false;
    job->error_flag = is_error;
    job->add_to_cache_db = (hash != NULL);
    if (hash != NULL) {
        job->hash_type = hash_type;
        memcpy(job->hash, hash, SHA256_HASH_LENGTH);
    }
    job->show_progress = true;

    *(g_fol_runner->jobs_tail) = job;
    g_fol_runner->jobs_tail = &(job->next);
    ++(g_fol_runner->num_jobs);

    if (is_error) {
        g_fol_runner->error_found = true;
    }
}

// Determine if a job is 'done'.
// Also sets *unsat to true if the result was unsat.
static bool is_job_done(struct Job *job, bool *unsat)
{
    // If a prover has found 'sat' or 'unsat' then the job is done,
    // even if other provers are still running.
    bool found_running = false;

    for (int i = 0; i < job->num_started; ++i) {
        struct Process *proc = &job->procs[i];

        switch (proc->status) {
        case PROC_RUNNING:
            found_running = true;
            break;

        case PROC_SUCCESS:
            if (is_sat(proc->output, proc->output_length)) {
                return true;
            } else if (is_unsat(proc->output, proc->output_length)) {
                *unsat = true;
                return true;
            }
            break;

        case PROC_TIMED_OUT:
        case PROC_FAILED_TO_START:
            break;
        }
    }

    // OK, nobody found 'sat' or 'unsat' yet, so the job is done if
    // and only if all provers have finished running. (And it is not
    // 'unsat'.)
    return (job->num_started == NUM_PROVERS && !found_running);
}

// Append msg to job->completion_msg (if needed).
// Hands over msg.
static void set_completion_msg(struct Job *job, char *msg)
{
    if (job->completion_msg) {
        char *msg2 = copy_string_2(job->completion_msg, msg);
        free((char*)job->completion_msg);
        free(msg);
        job->completion_msg = msg2;
    } else {
        job->completion_msg = msg;
    }
}

// Create a message to be printed regarding a 'done' job.
static void fill_completion_msg(struct Job *job)
{
    // First of all, if any job has an unexpected output, we should
    // include that in the message
    for (int i = 0; i < job->num_started; ++i) {
        struct Process *proc = &job->procs[i];
        if (proc->status == PROC_SUCCESS) {
            if (!is_sat(proc->output, proc->output_length)
            && !is_unsat(proc->output, proc->output_length)
            && !is_unknown(proc->output, proc->output_length)) {
                // null-terminate the output for printing
                if (proc->output_length < MAX_OUTPUT) {
                    proc->output[proc->output_length] = 0;
                } else {
                    proc->output[MAX_OUTPUT - 1] = 0;
                }

                char *msg =
                    copy_string_5("\n\nWARNING: unexpected output from prover [",
                                  proc->cmd[0],
                                  "]: ",
                                  proc->output,
                                  "\n");
                set_completion_msg(job, msg);
            }
        }
    }

    // Let's see if any job completed with sat or unsat, and therefore
    // we can print an appropriate message. (Also look for timeouts
    // etc. while we're here.)
    bool found_timeout = false;
    bool all_failed_to_start = true;
    for (int i = 0; i < job->num_started; ++i) {
        struct Process *proc = &job->procs[i];
        if (proc->status == PROC_SUCCESS) {
            if (is_sat(proc->output, proc->output_length)) {
                char *msg = copy_string_3(" (",
                                          proc->cmd[0],
                                          " returned 'sat')\n");
                set_completion_msg(job, msg);
                return;

            } else if (is_unsat(proc->output, proc->output_length)) {
                char buf[50];
                sprintf(buf, ", %.1fs)\n", proc->runtime_in_seconds);
                char *msg = copy_string_3(" (",
                                          proc->cmd[0],
                                          buf);
                set_completion_msg(job, msg);
                return;
            }
        } else if (proc->status == PROC_TIMED_OUT) {
            found_timeout = true;
        }
        if (proc->status != PROC_FAILED_TO_START) {
            all_failed_to_start = false;
        }
    }

    if (found_timeout) {
        set_completion_msg(job, copy_string(" (timed out)\n"));
    } else if (all_failed_to_start) {
        // If one prover fails to start, we do not currently report this, as e.g. it might
        // just not be installed on the user's machine.
        // If all provers fail to start, clearly there is a problem, so we have a special
        // message for this.
        set_completion_msg(job, copy_string(" (failed, provers could not be executed)\n"));
    } else {
        // At least one prover successfully executed, but it returned
        // neither 'sat' nor 'unsat'.
        set_completion_msg(job, copy_string(" (provers gave up)\n"));
    }
}

// Kill any still running processes in a job.
static void kill_job_processes(struct Job *job)
{
    for (int i = 0; i < job->num_started; ++i) {
        if (job->procs[i].status == PROC_RUNNING) {
            kill_process(&job->procs[i]);
        }
    }
}

static bool has_running_processes(const struct Job *job)
{
    for (int i = 0; i < job->num_started; ++i) {
        if (job->procs[i].status == PROC_RUNNING) {
            return true;
        }
    }
    return false;
}

// Update a single job - not starting any new processes, but checking
// for completed processes and the like.
// Returns true if the job should be dropped from the head of the list.
static bool update_job(struct Job *job)
{
    // If the job is active, but 'done', then we can set active to false,
    // and do other required updates.
    if (job->active) {
        bool unsat = false;
        if (is_job_done(job, &unsat)) {
            job->active = false;

            // Try to terminate the other processes (if any) as they
            // did not "win" the race.
            kill_job_processes(job);

            // Set completion message ("(z3, 1.0s)" or "(timed out)"
            // or whatever).
            fill_completion_msg(job);

            if (unsat) {
                // Proof found; do not print the error msg.

                // Also store the successful proof in the cache. (We
                // do this immediately, rather than waiting for the
                // job to reach the front of the list, so that future
                // jobs can benefit from the caching as early as
                // possible. We do NOT go through and re-evaluate
                // whether any existing jobs could be killed or
                // removed due to this new cache entry, but maybe we
                // could.)

                free((char*)job->error_msg);
                job->error_msg = NULL;
                add_sha256_to_db(g_fol_runner->cache_db, SMT_QUERY_HASH, job->hash);

            } else {
                // Proof NOT found; retain the error msg, set error_flag.
                // Also set error_found flag in the runner.
                job->error_flag = true;
                g_fol_runner->error_found = true;
            }
        }
    }

    // If the job is at the start of the list, then print any required
    // messages.
    if (job == g_fol_runner->jobs_head) {

        // Don't print anything to do with jobs beyond the first error,
        // UNLESS continue_after_error is true.
        if (!g_fol_runner->error_reached || g_fol_runner->continue_after_error) {
            if (job->announce_msg != NULL && job->show_progress) {
                fprintf(stderr, "%s", job->announce_msg);
                free((char*)job->announce_msg);
                job->announce_msg = NULL;
            }

            if (!job->active && job->completion_msg && job->show_progress) {
                fprintf(stderr, "%s", job->completion_msg);
                free((char*)job->completion_msg);
                job->completion_msg = NULL;
            }

            if (!job->active && job->error_msg) {
                fprintf(stderr, "%s", job->error_msg);
                free((char*)job->error_msg);
                job->error_msg = NULL;
            }
        }
    }

    // If the job is at the start of the list, and had an error, then
    // set error_reached.
    if (job == g_fol_runner->jobs_head && job->error_flag) {
        g_fol_runner->error_reached = true;
    }

    // If error_reached and !continue_after_error, then we want to
    // wind up the queue -- kill all remaining child processes, and
    // set all remaining jobs to inactive.
    if (g_fol_runner->error_reached && !g_fol_runner->continue_after_error) {
        kill_job_processes(job);
        job->active = false;
    }

    // If the job is at the start of the list, !active,
    // add_to_cache_db, and !error_reached, then add an item to the
    // DB. (This is used for updating the module and decl level
    // caches.)
    if (job == g_fol_runner->jobs_head
    && !job->active
    && job->add_to_cache_db
    && !g_fol_runner->error_reached) {
        add_sha256_to_db(g_fol_runner->cache_db, job->hash_type, job->hash);
        job->add_to_cache_db = false;
    }

    // Remove the job from the list if:
    //  - It is at the head of the list.
    //  - It is not active (i.e. we have obtained a result).
    //  - All processes have exited (or been killed).
    return (job == g_fol_runner->jobs_head && !job->active && !has_running_processes(job));
}

// This kicks off processes (for all jobs, starting from the front of the list)
// until we have reached the maximum allowed number of parallel processes.
static void start_new_processes(int num_running)
{
    // After an error is reached, we no longer start new processes
    // (unless continue_after_error is set).
    if (g_fol_runner->error_reached && !g_fol_runner->continue_after_error) {
        return;
    }

    for (struct Job *job = g_fol_runner->jobs_head; job; job = job->next) {
        while (job->active && job->num_started < NUM_PROVERS) {

            // Stop here if we already have enough processes running.
            if (num_running >= MAX_PROVER_PROCESSES) {
                return;
            }

            // Start the new process.
            launch_process(&job->procs[job->num_started]);
            ++(job->num_started);
            ++num_running;

            if (job->num_started == NUM_PROVERS) {
                // That was the last process for this job. We can free smt_problem now.
                free_sexpr(job->smt_problem);
                job->smt_problem = NULL;
            }
        }
    }
}

void update_fol_status()
{
    // Get updates from the Process subsystem (process.h).
    update_processes(false);

    // Update all Jobs as necessary.
    // Also count how many processes we have running.
    int running_processes = 0;
    for (struct Job *job = g_fol_runner->jobs_head; job; ) {
        bool remove = update_job(job);

        if (remove) {
            if (job != g_fol_runner->jobs_head) fatal_error("only jobs at head of list can be removed");

            // remove job from list
            g_fol_runner->jobs_head = job->next;
            if (job->next == NULL) g_fol_runner->jobs_tail = &g_fol_runner->jobs_head;
            --(g_fol_runner->num_jobs);

            // free the job
            free_job(job);

            // move on
            job = g_fol_runner->jobs_head;

        } else {
            // count processes
            for (int i = 0; i < job->num_started; ++i) {
                if (job->procs[i].status == PROC_RUNNING) {
                    ++running_processes;
                }
            }

            // move on
            job = job->next;
        }
    }

    // Start new processes if required.
    start_new_processes(running_processes);
}

void wait_fol_complete()
{
    if (g_fol_runner) {
        while (g_fol_runner->jobs_head) {
            update_processes(true);
            update_fol_status(g_fol_runner);
        }
    }
}

bool fol_error_found()
{
    return g_fol_runner->error_found;
}
