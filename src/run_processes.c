/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#define _POSIX_C_SOURCE 200112L

#include "alloc.h"
#include "error.h"
#include "run_processes.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

// Uncommenting the following will allow stderr messages from the child
// processes to be printed. This can be useful e.g. to check whether the
// child processes are starting correctly or not.
//#define DEBUG_OUTPUT


// ------------------------------------------------------------------------

struct ProcInfo {
    pid_t pid;
    int child_stdout;  // -1 if child no longer running (or failed to start)
};

struct JobState {
    struct Job *job;
    struct ProcInfo *infos;
    bool sent_sigint;
    bool sent_sigkill;
    struct timespec start_time;  // Time job started. Reset when signal sent
};

// ------------------------------------------------------------------------

static void get_current_time(struct timespec *t)
{
    int clock_result = clock_gettime(CLOCK_MONOTONIC, t);
    if (clock_result < 0) {
        fatal_error("clock_gettime failed");
    }
}

// returns true if time1 > time2
static bool time_greater(const struct timespec *time1, const struct timespec *time2)
{
    return (time1->tv_sec > time2->tv_sec)
        || (time1->tv_sec == time2->tv_sec
            && time1->tv_nsec > time2->tv_nsec);
}

// returns time1 - time2
static struct timespec diff_time(const struct timespec *time1, const struct timespec *time2)
{
    struct timespec diff;
    diff.tv_sec = time1->tv_sec - time2->tv_sec;
    diff.tv_nsec = time1->tv_nsec - time2->tv_nsec;
    if (diff.tv_nsec < 0) {
        diff.tv_nsec += 1000000000;
        diff.tv_sec --;
    }
    return diff;
}

// ------------------------------------------------------------------------

bool g_got_sigchld = false;

static void sigchld_handler(int sig)
{
    g_got_sigchld = true;
}

static void setup_signals()
{
    static bool done = false;
    if (done) return;
    done = true;

    // ignore SIGPIPE
    {
        struct sigaction sa;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sa.sa_handler = SIG_IGN;
        if (sigaction(SIGPIPE, &sa, NULL) < 0) {
            fatal_error("sigaction failed");
        }
    }

    // block SIGCHLD
    {
        sigset_t sigmask;
        sigemptyset(&sigmask);
        sigaddset(&sigmask, SIGCHLD);
        if (sigprocmask(SIG_BLOCK, &sigmask, NULL) < 0) {
            fatal_error("sigprocmask failed");
        }
    }

    // handle SIGCHLD
    {
        struct sigaction sa;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sa.sa_handler = sigchld_handler;
        if (sigaction(SIGCHLD, &sa, NULL) < 0) {
            fatal_error("sigaction failed");
        }
    }
}

// ------------------------------------------------------------------------

static void init_job_state(struct JobState *state, struct Job *job)
{
    state->job = job;

    state->infos = alloc(sizeof(struct ProcInfo) * job->num_procs);
    for (int i = 0; i < job->num_procs; ++i) {
        state->infos[i].pid = 0;
        state->infos[i].child_stdout = -1;
        state->job->procs[i].output_length = 0;
        state->job->procs[i].interrupted = false;
    }

    state->sent_sigint = state->sent_sigkill = false;
    get_current_time(&state->start_time);
}

static void destroy_job_state(struct JobState *state)
{
    free(state->infos);
}

// ------------------------------------------------------------------------

static void fork_child(struct Job *job, struct Process *proc, struct ProcInfo *info)
{
    // pipes[0]: child stdin. (read end) (write end)
    // pipes[1]: child stdout. (read end) (write end)
    int pipes[2][2];

    if (pipe(pipes[0]) != 0) {
        return;
    }
    if (pipe(pipes[1]) != 0) {
        close(pipes[0][0]);
        close(pipes[0][1]);
        return;
    }

    pid_t child_pid = fork();

    if (child_pid == -1) {
        // Fork failed
        close(pipes[0][0]);
        close(pipes[0][1]);
        close(pipes[1][0]);
        close(pipes[1][1]);

    } else if (child_pid == 0) {
        // This is the child process

        close(pipes[0][1]);
        close(pipes[1][0]);

        if (dup2(pipes[0][0], STDIN_FILENO) == -1 || dup2(pipes[1][1], STDOUT_FILENO) == -1) {
            exit(1);
        }

        close(pipes[0][0]);
        close(pipes[1][1]);

#ifndef DEBUG_OUTPUT
        // Let's redirect stderr to null to prevent unwanted messages such as
        // "cvc5 interrupted by user"
        int devnull = open("/dev/null", O_WRONLY);
        if (devnull == -1) {
            exit(1);
        }
        if (dup2(devnull, STDERR_FILENO) == -1) {
            exit(1);
        }
#endif

        execvp(proc->cmd[0], (char * const*) proc->cmd);

        // Error
        // (Note: the message will go to stderr, so it will only be visible
        // if DEBUG_OUTPUT is defined)
        fprintf(stderr, "couldn't start prover: %s\n", proc->cmd[0]);
        perror("exec failed");
        exit(1);

    } else {
        // This is the parent process
        info->pid = child_pid;

        close(pipes[0][0]);
        close(pipes[1][1]);

        FILE *child_input = fdopen(pipes[0][1], "w");
        if (child_input) {
            job->print_to_stdin(job->context, child_input);
            fclose(child_input);
        } else {
            close(pipes[0][1]);
        }

        info->child_stdout = pipes[1][0];
    }
}

static void fork_children(struct JobState *state)
{
    for (int i = 0; i < state->job->num_procs; ++i) {
        fork_child(state->job, &state->job->procs[i], &state->infos[i]);
    }
}


// ------------------------------------------------------------------------

// If just one process still running, return its name.
static const char * still_running_process_name(struct JobState *state)
{
    const char *result = NULL;
    for (int i = 0; i < state->job->num_procs; ++i) {
        if (state->infos[i].pid != 0) {
            if (result) {
                // Multiple processes still running
                return NULL;
            } else {
                result = state->job->procs[i].cmd[0];
            }
        }
    }
    return result;
}

// Returns true if any processes are still running, false if all have exited.
static bool wait_for_data(struct JobState *state)
{
    // Create a set of all running fds.
    fd_set fds;
    int nfds = 0;
    FD_ZERO(&fds);

    bool found_pid = false;

    for (int i = 0; i < state->job->num_procs; ++i) {
        int fd = state->infos[i].child_stdout;
        if (fd >= 0) {
            FD_SET(fd, &fds);
            if (fd + 1 > nfds) {
                nfds = fd + 1;
            }
        }

        if (state->infos[i].pid != 0) {
            found_pid = true;
        }
    }

    if (nfds == 0 && !found_pid) {
        return false;
    }

    // Time calculations
    struct timespec end_time = state->start_time;
    end_time.tv_sec += state->job->timeout_in_seconds;

    struct timespec time_now;
    get_current_time(&time_now);

    // Create empty signal mask (for pselect call) and also clear g_got_sigchld flag.
    sigset_t empty_mask;
    sigemptyset(&empty_mask);
    g_got_sigchld = false;


    // Wait for either:
    //  (a) some child-process output to become readable; or
    //  (b) a child-process to exit; or
    //  (c) the timeout to be reached (and sigkill not sent yet).

    int select_result;

    if (state->sent_sigkill) {
        // pselect without timeout
        select_result = pselect(nfds, &fds, NULL, NULL, NULL, &empty_mask);

    } else if (time_greater(&end_time, &time_now)) {
        // pselect with timeout
        struct timespec timeout = diff_time(&end_time, &time_now);
        select_result = pselect(nfds, &fds, NULL, NULL, &timeout, &empty_mask);

    } else {
        // don't call pselect as we have already reached the timeout
        select_result = 0;
    }

    if (select_result < 0 && errno != EINTR) {
        // Select call returned an error.
        // (EINTR is expected, from SIGCHLD, but other errors are unexpected.)
        fatal_error("select failed");
    }

    if (select_result > 0) {
        // Data is ready for reading

        for (int i = 0; i < state->job->num_procs; ++i) {
            struct ProcInfo *info = &state->infos[i];
            struct Process *proc = &state->job->procs[i];

            int fd = info->child_stdout;
            if (fd >= 0 && FD_ISSET(fd, &fds)) {
                char buf[64];
                ssize_t nread = read(fd, buf, sizeof(buf));

                if (nread <= 0) {
                    // Read error, OR end-of-file.
                    // Close the fd.
                    close(fd);
                    info->child_stdout = -1;

                } else {
                    // Copy the received data into the output array.
                    int len = proc->output_length;
                    int n = MAX_OUTPUT - len;
                    if (nread < n) n = nread;
                    memcpy(&proc->output[len], buf, n);
                    proc->output_length += n;

                    // If we have reached the max output length then we
                    // might as well close the fd early.
                    if (proc->output_length == MAX_OUTPUT) {
                        close(fd);
                        info->child_stdout = -1;
                    }
                }
            }
        }

    } else if (select_result < 0) {
        if (g_got_sigchld) {
            // Try to reap each child process in turn
            for (int i = 0; i < state->job->num_procs; ++i) {
                if (state->infos[i].pid != 0) {
                    int wait_result = waitpid(state->infos[i].pid, NULL, WNOHANG);
                    if (wait_result < 0) {
                        fatal_error("waitpid failed");
                    } else if (wait_result > 0) {
                        // process no longer exists
                        state->infos[i].pid = 0;

                        // Check the output from the exited process.
                        // If should_stop returns true, that means we
                        // don't need to wait for the other processes.
                        // In this case we set timeout to zero, which
                        // will cause the next run of this function to
                        // start killing the child processes.
                        if (state->job->should_stop(state->job->context,
                                                    state->job->procs[i].output,
                                                    state->job->procs[i].output_length)
                        && !state->sent_sigint) {
                            state->job->timeout_in_seconds = 0;
                        }
                    }
                }
            }
        }
        // (else: we got some other signal; ignore it)

    } else {
        // Timeout expired

        // Decide whether to send SIGINT or SIGKILL
        int sig;
        if (!state->sent_sigint) {
            sig = SIGINT;
            state->sent_sigint = true;

            if (state->job->print_timeout_message && state->job->timeout_in_seconds > 0) {
                get_current_time(&time_now);
                struct timespec diff = diff_time(&time_now, &state->start_time);
                unsigned int sec = diff.tv_sec;
                if (diff.tv_nsec >= 500000000) ++sec;
                fprintf(stderr, "(timeout after %us)\n", sec);
                state->job->timeout = true;
            }

            // Allow 10 seconds before sending SIGKILL
            get_current_time(&state->start_time);
            state->job->timeout_in_seconds = 10;

        } else {
            // We already sent one signal, so send SIGKILL this time!
            sig = SIGKILL;
            state->sent_sigkill = true;
            if (state->job->print_timeout_message) {
                fprintf(stderr, "\nChild process");
                const char *name = still_running_process_name(state);
                if (name) {
                    fprintf(stderr, " '%s'", name);
                } else {
                    fprintf(stderr, "(es)");
                }
                fprintf(stderr, " didn't respond to SIGINT, sending SIGKILL...\n");
            }
        }

        // Send the signal to all children that are still running.
        for (int i = 0; i < state->job->num_procs; ++i) {
            if (state->infos[i].pid != 0) {
                kill(state->infos[i].pid, sig);
                state->job->procs[i].interrupted = true;
            }

            // Also close their fd, as we no longer care about what they are writing.
            if (state->infos[i].child_stdout >= 0) {
                close(state->infos[i].child_stdout);
                state->infos[i].child_stdout = -1;
            }
        }
    }

    return true;
}

void run_processes(struct Job *job)
{
    struct timespec start_time;
    get_current_time(&start_time);

    job->timeout = false;
    job->time_in_seconds = 0.0;

    setup_signals();

    struct JobState state;
    init_job_state(&state, job);

    fork_children(&state);

    while (wait_for_data(&state));

    destroy_job_state(&state);

    struct timespec fin_time;
    get_current_time(&fin_time);
    struct timespec diff = diff_time(&fin_time, &start_time);
    job->time_in_seconds = ((double)diff.tv_sec) + ((double)diff.tv_nsec)/1e9;
}
