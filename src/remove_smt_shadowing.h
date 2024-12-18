/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef REMOVE_SMT_SHADOWING_H
#define REMOVE_SMT_SHADOWING_H

struct Sexpr;

// Remove "variable shadowing" from an SMT-LIB problem by
// alpha-renaming bound variables.
void remove_smt_shadowing(struct Sexpr *problem);

#endif
