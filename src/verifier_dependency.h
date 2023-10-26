/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_DEPENDENCY_H
#define VERIFIER_DEPENDENCY_H

struct Component;
struct HashTable;
struct Sexpr;

// Analyse the dependencies of expr1 and expr2.

// The result is a set of Components in which the "vertex_data" is a char*
// pointer containing a FOL name.

// env1 and env2 are mappings from FOL-name to Item* (either can be NULL).

struct Component * get_sexpr_dependencies(const struct HashTable *env1,
                                          const struct HashTable *env2,
                                          const struct Sexpr *expr1,
                                          const struct Sexpr *expr2);

#endif
