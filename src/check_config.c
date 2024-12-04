/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "check_config.h"
#include "check_prover.h"
#include "config_file.h"
#include "process.h"
#include "util.h"

#include <stdio.h>
#include <stdlib.h>

static bool test_compiler_command(const char *name, const char *cmd)
{
    printf(" - Checking %s [%s]\n", name, cmd);

    struct Process proc;
    default_init_process(&proc);
    const char * cmd_array[] = { cmd, NULL };
    proc.cmd = cmd_array;
    launch_process(&proc);
    while (proc.status == PROC_RUNNING) update_processes(true);

    return (proc.status == PROC_SUCCESS);
}

bool check_config(struct CompilerConfig *cfg)
{
    printf("\n");
    printf("Config file location: %s\n", cfg->config_filename);

    // Check C compiler tools.
    printf("\n");
    printf("Checking C compiler config:\n");
    bool cc_ok = test_compiler_command("C compiler", cfg->c_compiler);
    bool ld_ok = test_compiler_command("linker", cfg->linker);
    bool pkg_config_ok = test_compiler_command("pkg-config utility", cfg->pkg_config);

    // Check configured provers.
    printf("\n");
    printf("Checking prover config:\n");
    char *bad_provers = NULL;
    for (struct ProverConfig *pr = cfg->provers; pr; pr = pr->next) {
        bool ok = check_prover(pr);
        if (!ok) {
            if (bad_provers == NULL) {
                bad_provers = copy_string(pr->name);
            } else {
                char *str = copy_string_3(bad_provers, ", ", pr->name);
                free(bad_provers);
                bad_provers = str;
            }
        }
    }

    // Summary.
    printf("\n");
    printf("Summary:\n");
    bool all_ok = true;
    if (!cc_ok || !ld_ok) {
        printf(" - C compiler and/or linker are not working. 'bab compile' will not\n"
               "   be available.\n"
               "    - Recommendation: Check that your C compiler is installed correctly\n"
               "      and that the values 'c-compiler.cc' and 'c-compiler.ld' in\n"
               "      babylon.toml are correct.\n");
        all_ok = false;
    }
    if (!pkg_config_ok) {
        printf(" - Pkg-config is not working. Babylon packages that use external\n"
               "   dependencies ('system-packages') will not be compilable.\n"
               "    - Recommendation: Check that pkg-config is installed and that the\n"
               "      value of 'c-compiler.pkg-config' in babylon.toml is correct.\n");
        all_ok = false;
    }
    if (bad_provers) {
        printf(" - The following provers are not configured correctly: [%s]\n", bad_provers);
        free(bad_provers);
        printf("   'bab verify' may not work correctly.\n"
               "    - Recommendation: Check the 'provers' section of babylon.toml.\n");
        all_ok = false;
    } else if (cfg->provers == NULL) {
        printf(" - No provers are configured. 'bab verify' will not be available.\n"
               "    - Recommendation: Add one or more items to the 'provers' section\n"
               "      of babylon.toml.\n");
        all_ok = false;
    }

    if (all_ok) {
        printf(" - All checks passed. No action required.\n");
    }

    printf("\n");

    return all_ok;
}
