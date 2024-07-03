/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_DEPENDENCY_H
#define VERIFIER_DEPENDENCY_H

struct HashTable;
struct Sexpr;
struct StackedHashTable;

// Get all free variable names in sexpr, e.g.
// (+ %x (let ((%y 1)) %y)) will return "%x" but not "%y".
void get_free_var_names_in_sexpr(const struct Sexpr *expr,
                                 struct HashTable *var_names,
                                 struct HashTable *scratch);


// Analyse the dependencies of expr.

// "stack" maps from FOL-name to Item*.

// If use_all_layers is true, uses all layers of the stack, otherwise uses only the top layer.

// The result is a single sexpr containing a list of all declarations,
// definitions and asserts that are relevant to expr (in a random order).
// The given "tail_sexpr" (which is handed over) will also be appended
// to the result.

struct Sexpr * get_sexpr_dependencies(const struct StackedHashTable *stack,
                                      bool use_all_layers,
                                      const struct HashTable *hidden_names,
                                      const struct Sexpr *expr,
                                      struct Sexpr *tail_sexpr);


// Reorder a list of definitions to respect the dependency order.
// (The original list is handed over and a new list is returned.)

struct Sexpr * reorder_sexpr_defns(struct Sexpr *defns, bool reverse_order);

#endif
