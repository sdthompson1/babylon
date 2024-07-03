/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef VERIFIER_H
#define VERIFIER_H

#include "location.h"
#include "sha256.h"

#include <stdbool.h>

struct CacheDb;
struct Module;
struct Sexpr;
struct VerifierEnv;


struct VerifierEnv * new_verifier_env();
void free_verifier_env(struct VerifierEnv *);

void push_verifier_env(struct VerifierEnv *);
void pop_verifier_env(struct VerifierEnv *);
void collapse_verifier_env(struct VerifierEnv *);

struct HashTable * detach_verifier_env_layer(struct VerifierEnv *);
void attach_verifier_env_layer(struct VerifierEnv *, struct HashTable *);

enum VerifierMode {
    VM_LOAD_INTERFACE,
    VM_CHECK_INTERFACE,
    VM_LOAD_INTERFACE_CHECK_IMPL
};

struct VerifierOptions {
    struct CacheDb *cache_db;
    const char *debug_filename_prefix;
    enum VerifierMode mode;
    bool show_progress;
    // note: settings for timeout, and whether to continue after error,
    // are determined by the FolRunner
};


// Verify the module. Returns true if valid, false if error found.
// (Any error messages are printed to stderr.)

// Also adds Items to the (topmost layer of the) verifier_env.

bool verify_module(struct VerifierEnv *verifier_env,
                   struct Module *module,
                   struct VerifierOptions *options);

#endif
