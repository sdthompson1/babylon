/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_STATEMENTS_H
#define VERIFIER_STATEMENTS_H

#include "location.h"

#include <stdbool.h>

struct Sexpr;
struct Statement;
struct VContext;

bool verify_postconditions(struct VContext *context,
                           struct Location loc,
                           struct Sexpr *ret_val);

bool verify_statements(struct VContext *context,
                       struct Statement *stmt,
                       struct Sexpr *** ret_val_ptr);

#endif
