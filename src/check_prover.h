/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef CHECK_PROVER_H
#define CHECK_PROVER_H

#include <stdbool.h>

struct ProverConfig;

// Checking whether a string is "unsat", "sat" or "unknown" (possibly
// with leading white space).
bool is_unsat(const char *buf, int length);
bool is_sat(const char *buf, int length);
bool is_unknown(const char *buf, int length);


// Check whether a configured prover is working.
// This prints appropriate messages to stdout (and stderr if it fails).
// Returns true if the test is successful.
bool check_prover(struct ProverConfig *config);


// Enum for standard, "known" provers.
enum StandardProver {
    PROVER_Z3 = 0,
    PROVER_CVC5,
    PROVER_CVC4,
    PROVER_VAMPIRE,
    PROVER_ALT_ERGO,
    NUM_STD_PROVERS
};

// Return the name of a standard prover.
// Returns static string.
const char * standard_prover_name(enum StandardProver prover);

// Detect whether a given prover is installed on the system, or not.
// Returns true if successful.
// Also returns (in *config) an allocated string to paste into the config file
// (this will be "commented out" if the auto-detection failed).
bool detect_standard_prover(enum StandardProver prover, char **config);


#endif
