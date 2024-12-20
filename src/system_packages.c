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
#include <string.h>

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
    bool found_math = false;

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
        // "math" is not sent to pkg-config but interpreted specially
        if (strcmp(node->name, "math") == 0) {
            found_math = true;
        } else {
            cmd[i] = copy_string_3(node->name, " >= ", node->min_version);
            ++i;
        }
    }
    cmd[i] = NULL;

    bool pkg_config_error = false;
    if (output_list) *output_list = NULL;

    if (i > 2) {  // if i <= 2, then there are no system packages, so do not run pkg-config

        struct Process proc;
        default_init_process(&proc);
        proc.cmd = cmd;
        proc.show_stderr = true;

        launch_process(&proc);
        while (proc.status == PROC_RUNNING) {
            update_processes(true);
        }

        if (proc.status == PROC_SUCCESS && proc.exit_status == 0) {
            // pkg-config returned status 0 which means that it successfully printed
            // the cflags or libs. Put these in "output_list".
            if (output_list) *output_list = split_string(proc.output, proc.output_length);
        } else {
            // There are two cases:
            // (1) The pkg-config process failed to start (proc.status != PROC_SUCCESS):
            //   Print an error message so that the user can debug (e.g.: maybe pkg-config is
            //   not installed, or "pkg-config" is not set correctly in the compiler config
            //   file).
            // (2) The pkg-config process ran to completion but returned non-zero exit status:
            //   pkg-config would have already printed some error messages on stderr, so we
            //   don't need to do anything else.
            if (proc.status != PROC_SUCCESS) {
                fprintf(stderr, "Error: Could not resolve system-packages: pkg-config command failed.\n");
            }
            pkg_config_error = true;
        }
    }

    for (i = 2; cmd[i] != NULL; ++i) {
        free((char*)cmd[i]);
    }
    free(cmd);
    cmd = NULL;

    if (pkg_config_error) {
        return false;
    }

    // If "math" was requested (at any version) then add "-lm"
    // (for --libs only)
    if (output_list && found_math && strcmp(request, "--libs") == 0) {
        struct NameList *node = alloc(sizeof(struct NameList));
        node->name = copy_string("-lm");
        node->next = *output_list;
        *output_list = node;
    }

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
