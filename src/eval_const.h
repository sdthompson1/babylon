/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef EVAL_CONST_H
#define EVAL_CONST_H

#include <stdint.h>

struct HashTable;
struct Term;

// Returns a newly allocated Term, or NULL if the input term is not a
// compile-time constant.

struct Term * eval_to_normal_form(struct HashTable *type_env,
                                  struct Term *term);

#endif
