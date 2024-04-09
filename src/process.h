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
#define MAX_OUTPUT 200

// Status codes for a child process.
enum ProcStatus {
    PROC_RUNNING,
    PROC_SUCCESS,
    PROC_TIMED_OUT,
    PROC_FAILED_TO_START
};

// Struct representing a child process.
struct Process {
    // Input
    const char ** cmd;

    void (*print_to_stdin)(void *context, FILE *pipe);
    void *context;

    int timeout_in_seconds;

    // Output
    enum ProcStatus status;

    double runtime_in_seconds;

    char output[MAX_OUTPUT];
    int output_length;
};

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
