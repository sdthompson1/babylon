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


// Check whether there are any unresolved TY_UNIVAR types within the
// given type, term, statement or decl.
bool type_contains_unresolved_univars(struct Type *type);
bool term_contains_unresolved_univars(struct Term *term);
bool statement_contains_unresolved_univars(struct Statement *stmt);  // checks one stmt (not the whole list)
bool decl_contains_unresolved_univars(struct Decl *decl);  // checks one decl (not the whole list)


// Remove all TY_UNIVAR types, replacing them with their actual
// post-unification type. (Unresolved univars are left alone.)
void remove_univars_from_type(struct Type *type);
void remove_univars_from_term(struct Term *term);
void remove_univars_from_statement(struct Statement *stmt);  // processes one stmt (not the whole list)
void remove_univars_from_decl(struct Decl *decl);  // processes one decl (not the whole list)

#endif
