/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_DEPENDENCY_H
#define VERIFIER_DEPENDENCY_H

struct HashTable;
struct Sexpr;

// Analyse the dependencies of expr.

// env1 and env2 are mappings from FOL-name to Item* (either can be NULL).

// The result is a single sexpr containing a list of all declarations,
// definitions and asserts that are relevant to expr (in a random order).
// The given "tail_sexpr" (which is handed over) will also be appended
// to the result.

struct Sexpr * get_sexpr_dependencies(const struct HashTable *env1,
                                      const struct HashTable *env2,
                                      const struct Sexpr *expr,
                                      struct Sexpr *tail_sexpr);


// Reorder a list of definitions to respect the dependency order.
// (The original list is handed over and a new list is returned.)

struct Sexpr * reorder_sexpr_defns(struct Sexpr *defns, bool reverse_order);

#endif
