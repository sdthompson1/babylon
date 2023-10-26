/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef RUN_PROCESSES_H
#define RUN_PROCESSES_H

#include <stdbool.h>
#include <stdio.h>

#define MAX_OUTPUT 200

struct Process {
    // input
    const char ** cmd;

    // output
    char output[MAX_OUTPUT];
    int output_length;
    bool interrupted;
};

struct Job {
    struct Process *procs;
    int num_procs;

    int timeout_in_seconds;
    bool print_timeout_message;

    void (*print_to_stdin)(void *context, FILE *pipe);
    bool (*should_stop)(void *context, const char *output, int output_length);
    void *context;

    // output values
    bool timeout;
    double time_in_seconds;
};

void run_processes(struct Job *job);

#endif
