/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#define _POSIX_C_SOURCE 200112L

#include "alloc.h"
#include "error.h"
#include "process.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/signalfd.h>
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

struct ProcessState {
    struct ProcessState *next;
    struct Process *process;

    bool sent_sigint;
    bool sent_sigkill;

    pid_t pid;                   // 0 if process no longer exists.
    int child_stdout;            // -1 if not open.

    struct timespec start_time;  // Time process started.
    struct timespec kill_time;   // Valid if pid != 0 && !sent_sigkill. Time next signal to be sent.
};

struct ProcessState * g_process_states = NULL;

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

// returns true if time1 >= time2
static bool time_greater_or_equal(const struct timespec *time1, const struct timespec *time2)
{
    return !time_greater(time2, time1);
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

int g_sigfd = -1;

static void setup_signals()
{
    // This should only run once.
    if (g_sigfd != -1) {
        return;
    }

    // Ignore SIGPIPE.
    {
        struct sigaction sa;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sa.sa_handler = SIG_IGN;
        if (sigaction(SIGPIPE, &sa, NULL) < 0) {
            fatal_error("sigaction failed");
        }
    }

    // Block SIGCHLD, and handle it via signalfd instead.
    {
        sigset_t sigmask;
        sigemptyset(&sigmask);
        sigaddset(&sigmask, SIGCHLD);
        if (sigprocmask(SIG_BLOCK, &sigmask, NULL) < 0) {
            fatal_error("sigprocmask failed");
        }
        g_sigfd = signalfd(-1, &sigmask, SFD_CLOEXEC);
        if (g_sigfd < 0) {
            fatal_error("signalfd failed");
        }
    }
}

// ------------------------------------------------------------------------

static void init_process_state(struct ProcessState *state, struct Process *process)
{
    state->next = NULL;
    state->process = process;
    state->sent_sigint = false;
    state->sent_sigkill = false;
    state->pid = 0;
    state->child_stdout = -1;
}

static void cleanup_process_states()
{
    struct ProcessState **state = &g_process_states;
    while (*state) {
        if ((*state)->pid == 0 && (*state)->child_stdout == -1) {
            // This process is complete. We can remove it from the list.
            if ((*state)->sent_sigint || (*state)->sent_sigkill) {
                (*state)->process->status = PROC_TIMED_OUT;
            } else {
                (*state)->process->status = PROC_SUCCESS;
            }
            struct ProcessState *to_free = *state;
            *state = (*state)->next;
            free(to_free);
        } else {
            state = &(*state)->next;
        }
    }
}

// ------------------------------------------------------------------------

static void fork_child(struct ProcessState *state)
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
        // Fork failed.
        close(pipes[0][0]);
        close(pipes[0][1]);
        close(pipes[1][0]);
        close(pipes[1][1]);

    } else if (child_pid == 0) {
        // This is the child process.

        close(pipes[0][1]);
        close(pipes[1][0]);

        if (dup2(pipes[0][0], STDIN_FILENO) == -1 || dup2(pipes[1][1], STDOUT_FILENO) == -1) {
            exit(1);
        }

        close(pipes[0][0]);
        close(pipes[1][1]);

        // Restore default SIGPIPE behaviour (it was ignored in the parent process).
        {
            struct sigaction sa;
            sigemptyset(&sa.sa_mask);
            sa.sa_flags = 0;
            sa.sa_handler = SIG_DFL;
            if (sigaction(SIGPIPE, &sa, NULL)) {
                perror("sigaction failed");
                exit(1);
            }
        }

        // Unblock SIGCHLD (it was blocked in the parent process).
        {
            sigset_t sigmask;
            sigemptyset(&sigmask);
            sigaddset(&sigmask, SIGCHLD);
            if (sigprocmask(SIG_UNBLOCK, &sigmask, NULL) < 0) {
                perror("sigprocmask failed");
                exit(1);
            }
        }

#ifndef DEBUG_OUTPUT
        // Let's redirect stderr to null to prevent unwanted messages such as
        // "cvc5 interrupted by user".
        int devnull = open("/dev/null", O_WRONLY);
        if (devnull == -1) {
            exit(1);
        }
        if (dup2(devnull, STDERR_FILENO) == -1) {
            exit(1);
        }
#endif

        // Call exec.
        execvp(state->process->cmd[0], (char * const*) state->process->cmd);

        // Error.
        // (Note: the message will go to stderr, so it will only be visible
        // if DEBUG_OUTPUT is defined)
        fprintf(stderr, "couldn't start prover: %s\n", state->process->cmd[0]);
        perror("exec failed");
        exit(1);

    } else {
        // This is the parent process

        state->pid = child_pid;

        close(pipes[0][0]);
        close(pipes[1][1]);

        FILE *child_input = fdopen(pipes[0][1], "w");
        if (child_input) {
            state->process->print_to_stdin(state->process->context, child_input);
            fclose(child_input);
        } else {
            close(pipes[0][1]);
        }

        state->child_stdout = pipes[1][0];

        get_current_time(&state->start_time);
        state->kill_time = state->start_time;
        state->kill_time.tv_sec += state->process->timeout_in_seconds;
    }
}


// ------------------------------------------------------------------------

// Read child process's stdout, and put it into the output array, if applicable.
// This also closes the FD on error, EOF, or the buffer filling up on our side.
// Returns true if any action was taken.
static bool read_child_process_output(struct ProcessState *state, const fd_set *fds)
{
    int fd = state->child_stdout;
    if (fd >= 0 && FD_ISSET(fd, fds)) {
        char buf[MAX_OUTPUT];
        ssize_t nread = read(fd, buf, sizeof(buf));

        if (nread <= 0) {
            // Read error, OR end-of-file.
            // Close the fd.
            close(fd);
            state->child_stdout = -1;

        } else {
            // Copy the received data into the output array.
            int len = state->process->output_length;
            int n = MAX_OUTPUT - len;
            if (nread < n) n = nread;
            memcpy(&state->process->output[len], buf, n);
            state->process->output_length += n;

            // If we have reached the max output length then we
            // might as well close the fd early.
            if (state->process->output_length == MAX_OUTPUT) {
                close(fd);
                state->child_stdout = -1;
            }
        }

        return true;

    } else {
        return false;
    }
}

// This reaps the child if it has exited.
static bool reap_child(struct ProcessState *state)
{
    if (state->pid != 0) {
        int wait_result = waitpid(state->pid, NULL, WNOHANG);
        if (wait_result < 0) {
            fatal_error("waitpid failed");

        } else if (wait_result > 0) {
            // process no longer exists
            state->pid = 0;

            // set the "runtime_in_seconds"
            // note this will only be as accurate as the frequency of calls to update_processes
            struct timespec time_now;
            get_current_time(&time_now);
            struct timespec runtime = diff_time(&time_now, &state->start_time);
            state->process->runtime_in_seconds =
                (double)runtime.tv_sec + (double)runtime.tv_nsec * 1e-9;

            return true;
        }
    }

    return false;
}

// This checks whether the process has reached its kill_time, and if so,
// sends an appropriate signal (and updates the state).
// Returns true if any action was taken.
static bool send_signal_if_required(struct ProcessState *state)
{
    struct timespec time_now;
    get_current_time(&time_now);

    if (state->pid != 0 && !state->sent_sigkill
    && time_greater_or_equal(&time_now, &state->kill_time)) {

        // Decide whether to send SIGINT or SIGKILL
        int sig;
        if (!state->sent_sigint) {
            sig = SIGINT;
            state->sent_sigint = true;

            // Allow 10 seconds before sending SIGKILL
            state->kill_time = time_now;
            state->kill_time.tv_sec += 10;

        } else {
            sig = SIGKILL;
            state->sent_sigkill = true;
        }

        // Send the signal
        kill(state->pid, sig);

        // Also close their FD, as we no longer care about what they are writing.
        if (state->child_stdout >= 0) {
            close(state->child_stdout);
            state->child_stdout = -1;
        }

        return true;
    } else {
        return false;
    }
}

// This updates all existing processes (e.g. reads from child stdout, reaps children).
// Returns true if anything was updated.
static bool check_processes(bool block)
{
    // Create a set of all running FDs.
    // Also calculate the min "kill_time" (over all processes for which kill_time is valid).

    fd_set fds;
    int nfds = 0;
    FD_ZERO(&fds);

    struct timespec time_now;
    get_current_time(&time_now);

    struct timespec min_kill_time = time_now;
    min_kill_time.tv_sec += 30;   // Capped at +30sec from now

    bool found_pid = false;

    for (struct ProcessState *state = g_process_states; state; state = state->next) {
        // Add the FD from this process to the set.
        int fd = state->child_stdout;
        if (fd >= 0) {
            FD_SET(fd, &fds);
            if (fd + 1 > nfds) {
                nfds = fd + 1;
            }
        }

        // Determine whether any process is currently running
        if (state->pid != 0) {
            found_pid = true;
        }

        // Update min_kill_time if applicable.
        if (state->pid != 0 && !state->sent_sigkill) {
            if (time_greater(&min_kill_time, &state->kill_time)) {
                min_kill_time = state->kill_time;
            }
        }
    }

    if (nfds == 0 && !found_pid) {
        // No running processes found, and no FDs to read from.
        // There is nothing for us to do.
        return false;
    }

    // Add our signal FD to the set.
    FD_SET(g_sigfd, &fds);
    if (g_sigfd + 1 > nfds) {
        nfds = g_sigfd + 1;
    }

    // Wait for either:
    //  (a) some child-process output to become readable; or
    //  (b) a child-process to exit (SIGCHLD read from g_sigfd); or
    //  (c) a valid 'kill_time' is reached.

    // (Or in non-blocking mode, just check whether any of these
    // conditions has occurred, without waiting.)

    int select_result;

    if (time_greater_or_equal(&time_now, &min_kill_time)) {
        // No need to call pselect as we have already reached a kill_time!
        select_result = 0;

    } else if (block) {
        // pselect with timeout that takes us up until "min_kill_time"
        struct timespec timeout = diff_time(&min_kill_time, &time_now);
        select_result = pselect(nfds, &fds, NULL, NULL, &timeout, NULL);

    } else {
        // non-blocking pselect
        struct timespec timeout;
        timeout.tv_sec = timeout.tv_nsec = 0;
        select_result = pselect(nfds, &fds, NULL, NULL, &timeout, NULL);
    }

    if (select_result < 0) {
        // Select call returned an error.
        fatal_error("select failed");
    }

    bool did_something = false;

    if (select_result > 0) {
        // Check if we can read any data from the child stdouts.
        for (struct ProcessState *state = g_process_states; state; state = state->next) {
            did_something = read_child_process_output(state, &fds) || did_something;
        }

        // Check if we can read anything from our signalfd.
        if (FD_ISSET(g_sigfd, &fds)) {
            // Read out the signalfd_siginfo structure, although we will ignore the contents.
            struct signalfd_siginfo dummy;
            ssize_t num_bytes = read(g_sigfd, &dummy, sizeof(dummy));
            if (num_bytes != sizeof(dummy)) {
                fatal_error("unexpected read from signalfd file descriptor");
            }
            // Try to reap each child process in turn.
            for (struct ProcessState *state = g_process_states; state; state = state->next) {
                did_something = reap_child(state) || did_something;
            }
        }
    }

    // Check timeouts.
    for (struct ProcessState *state = g_process_states; state; state = state->next) {
        did_something = send_signal_if_required(state) || did_something;
    }

    return did_something;
}

void update_processes(bool block)
{
    while (true) {
        bool updated = check_processes(block);

        if (updated) {
            cleanup_process_states();
        }

        // In blocking mode, just exit immediately -- as check_processes already has blocked
        // until an interesting event has occurred.
        // In non-blocking mode, keep looping until the update isn't "doing anything" any more.
        if (block || !updated) {
            return;
        }
    }
}

void launch_process(struct Process *process)
{
    setup_signals();   // one-time setup

    process->runtime_in_seconds = 0.0;
    process->output_length = 0;

    struct ProcessState *state = alloc(sizeof(struct ProcessState));
    init_process_state(state, process);

    fork_child(state);

    if (state->pid == 0) {
        process->status = PROC_FAILED_TO_START;
        free(state);

    } else {
        process->status = PROC_RUNNING;
        state->next = g_process_states;
        g_process_states = state;
    }
}

void kill_process(struct Process *proc)
{
    for (struct ProcessState *state = g_process_states; state; state = state->next) {
        if (state->process == proc && !state->sent_sigint) {
            // SIGINT not sent to this process yet. Set kill_time to
            // the current time which means we will send SIGINT at the
            // next opportunity.
            get_current_time(&state->kill_time);

            // Now actually send the signal.
            send_signal_if_required(state);

            // We found our process so no need to check the other ones.
            return;
        }
    }
}
