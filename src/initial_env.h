/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef INITIAL_ENV_H
#define INITIAL_ENV_H

#include "typechecker.h"

#include <stdint.h>

struct VerifierEnv;

void setup_initial_verifier_env(struct VerifierEnv *verifier_env);

#endif
