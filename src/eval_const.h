/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef EVAL_CONST_H
#define EVAL_CONST_H

#include "typechecker.h"

#include <stdint.h>

struct HashTable;
struct Term;

// Returns a newly allocated Term, or NULL if the input term is not a
// compile-time constant or contains an error (e.g. overflow or divide
// by zero).

// The input term is (currently) assumed to be a non-ghost term, e.g.
// casts to/from TY_MATH_INT are not allowed.

// If NULL is returned a suitable error message is printed.

struct Term * eval_to_normal_form(TypeEnv *type_env,
                                  struct Term *term);

#endif
