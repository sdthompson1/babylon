/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef MATCH_COMPILER_H
#define MATCH_COMPILER_H

#include <stdint.h>

struct Statement;
struct Term;

void match_compiler_attributes(uint64_t *name_counter, struct Attribute *attrs);

void match_compiler_statements(uint64_t *name_counter, struct Statement *stmts);

void match_compiler_term(uint64_t *name_counter, struct Term *term);

#endif
