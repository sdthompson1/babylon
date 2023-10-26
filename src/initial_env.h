/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef INITIAL_ENV_H
#define INITIAL_ENV_H

#include <stdint.h>

struct HashTable;
struct VerifierEnv;

void setup_initial_verifier_env(struct VerifierEnv *verifier_env);

bool import_builtin_module(const char *name,
                           struct HashTable *renamer_env,
                           struct HashTable *type_env,
                           struct VerifierEnv *verifier_env,
                           struct HashTable *codegen_env);

#endif
