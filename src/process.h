/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef PROCESS_H
#define PROCESS_H

#include <stdbool.h>
#include <stdio.h>

// Maximum number of stdout bytes (from the child process) that we keep.
#define MAX_OUTPUT 800

// Status codes for a child process.
enum ProcStatus {
    PROC_RUNNING,         // process is still running (or about to start running).
    PROC_SUCCESS,         // process ended "on its own" without us killing it. (exit_status will be valid.)
    PROC_TIMED_OUT,       // we killed the process due to timeout.
    PROC_FAILED_TO_START  // process never started in the first place (e.g. exec failure).
};

// Struct representing a child process.
struct Process {
    // Input
    const char ** cmd;

    void (*print_to_stdin)(void *context, FILE *pipe);   // can be NULL
    void *context;

    int timeout_in_seconds;
    int signal_num;  // Signal to send on initial timeout
    int kill_timeout_in_seconds;  // Time between initial timeout and sending SIGKILL. (<= 0 to disable.)

    // By default, stdout is captured to "output" array (below) and stderr
    // is redirected to /dev/null.
    // If show_stdout = true and/or show_stderr = true, then stdout and/or
    // stderr are just output normally instead.
    bool show_stdout;
    bool show_stderr;

    // Output
    enum ProcStatus status;
    int exit_status;  // as returned by WEXITSTATUS. set to -1 if WIFEXITED was false.

    double runtime_in_seconds;

    char output[MAX_OUTPUT];
    int output_length;
};

void default_init_process(struct Process *proc);

// Launch a new child process.
// The Process struct must not be released/freed until after the
// "status" value changes to something other than PROC_RUNNING, as
// "update_jobs" will write to the Output variables in the struct.
// However, the Input variables (including print_to_stdin) are no
// longer needed after this function returns.
void launch_process(struct Process *proc);

// This will update the Output variables in each running Process
// structure as needed, e.g. copying data into 'output' or updating
// 'status'.
// If block=true, will block until some significant update happens,
// otherwise it will just poll for updates and return.
void update_processes(bool block);

// Kill a process, this works by setting its timeout to zero
// (effectively), so it will change status to PROC_TIMED_OUT when it
// has disappeared. (TODO: Maybe we should have a separate PROC_KILLED
// status, but for now I don't need it, so this method works.)
void kill_process(struct Process *proc);

#endif
