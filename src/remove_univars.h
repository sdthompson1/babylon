/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef REMOVE_UNIVARS_H
#define REMOVE_UNIVARS_H

struct Type;
struct Term;
struct Attribute;
struct Statement;
struct Decl;

// Remove all TY_UNIVAR types, replacing them with their actual
// post-unification type, or with TY_BOOL if it was never actually
// unified with anything.

void remove_univars_from_type(struct Type *type);
void remove_univars_from_term(struct Term *term);
void remove_univars_from_attribute(struct Attribute *attr);
void remove_univars_from_statement(struct Statement *stmt);
void remove_univars_from_decl(struct Decl *decl);

#endif
