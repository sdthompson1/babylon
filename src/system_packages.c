/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "alloc.h"
#include "process.h"
#include "system_packages.h"

#include <ctype.h>
#include <stdlib.h>

static char* copy_string_section(const char *p, const char *q)
{
    char *result = alloc(q - p + 1);
    bool escape = false;
    char *out = result;
    for (const char *in = p; in != q; ++in) {
        if (*in == '\\' && !escape) {
            escape = true;
        } else {
            *out++ = *in;
            escape = false;
        }
    }
    *out = 0;
    return result;
}

static struct NameList * split_string(const char *str, int len)
{
    const char *end = str + len;

    struct NameList *result = NULL;
    struct NameList **tail = &result;

    const char *p = str;
    const char *q = str;
    bool escape = false;

    while (true) {
        if (q == end || (isspace(*q) && !escape)) {
            // we have a word
            if (q != p) {
                // we have a nonempty word
                struct NameList *node = alloc(sizeof(struct NameList));
                node->name = copy_string_section(p, q);
                node->next = NULL;
                *tail = node;
                tail = &node->next;
            }
            if (q == end) {
                break;
            }
            q++;    // skip the space
            p = q;  // start next word
        } else {
            escape = (*q == '\\' && !escape);
            q++;  // move to next character
        }
    }

    return result;
}

static bool run_pkg_config(const char *pkg_config_cmd,
                           struct DepList *packages,
                           const char *request,
                           struct NameList **output_list)
{
    if (packages == NULL) {
        // Nothing to do
        if (output_list) *output_list = NULL;
        return true;
    }

    int n = 0;
    for (struct DepList *node = packages; node; node = node->next) {
        ++n;
    }

    // pkg-config $(request) $(packages)
    const char **cmd = alloc(sizeof(const char*) * (n + 3));
    cmd[0] = pkg_config_cmd;
    cmd[1] = request;
    int i = 2;
    for (struct DepList *node = packages; node; node = node->next) {
        cmd[i] = copy_string_3(node->name, " >= ", node->min_version);
        ++i;
    }
    cmd[i] = NULL;

    struct Process proc;
    proc.cmd = cmd;
    proc.print_to_stdin = NULL;
    proc.timeout_in_seconds = 10000;
    proc.show_stdout = false;
    proc.show_stderr = true;

    launch_process(&proc);

    for (i = 2; i < 2 + n; ++i) {
        free((char*)cmd[i]);
    }
    free(cmd);
    cmd = NULL;

    while (proc.status == PROC_RUNNING) {
        update_processes(true);
    }

    if (proc.status != PROC_SUCCESS || proc.exit_status != 0) {
        if (output_list) *output_list = NULL;
        return false;
    }

    if (output_list) *output_list = split_string(proc.output, proc.output_length);
    return true;
}

bool system_package_cflags(const char *pkg_config_cmd,
                           struct DepList *packages,
                           struct NameList **output)
{
    return run_pkg_config(pkg_config_cmd, packages, "--cflags", output);
}

bool system_package_libs(const char *pkg_config_cmd,
                         struct DepList *packages,
                         struct NameList **output)
{
    return run_pkg_config(pkg_config_cmd, packages, "--libs", output);
}
