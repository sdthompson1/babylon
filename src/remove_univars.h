/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2026.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef REMOVE_UNIVARS_H
#define REMOVE_UNIVARS_H

#include <stdbool.h>

struct Type;
struct Term;
struct Statement;
struct Decl;
struct Location;


// Check whether there are any unresolved TY_UNIVAR types within the
// given type, term, statement or decl. If so, return the origin
// location of one of them, otherwise return NULL.
// (The returned pointer points into a UnivarNode, so it should be
// used before the univars are removed.)
const struct Location * find_unresolved_univar_in_type(struct Type *type);
const struct Location * find_unresolved_univar_in_term(struct Term *term);
const struct Location * find_unresolved_univar_in_statement(struct Statement *stmt);  // checks one stmt (not the whole list)
const struct Location * find_unresolved_univar_in_decl(struct Decl *decl);  // checks one decl (not the whole list)


// Remove all TY_UNIVAR types, replacing them with their actual
// post-unification type. (Unresolved univars are left alone.)
void remove_univars_from_type(struct Type *type);
void remove_univars_from_term(struct Term *term);
void remove_univars_from_statement(struct Statement *stmt);  // processes one stmt (not the whole list)
void remove_univars_from_decl(struct Decl *decl);  // processes one decl (not the whole list)

#endif
