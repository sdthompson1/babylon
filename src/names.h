/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef NAMES_H
#define NAMES_H

struct Decl;
struct HashTable;
struct Term;
struct Type;

// Each of these will ADD the names in the given object to the given HashTable
// (with 'value' of NULL.)

// Note that datatype field names are not included.

void names_used_in_type(struct HashTable *names, struct Type *type);

void names_used_in_term(struct HashTable *names, struct Term *term);

void names_used_in_statements(struct HashTable *names, struct Statement *stmt);

void names_used_in_decl(struct HashTable *names, struct Decl *decl);


// Add all variables *modified* by a statement (e.g., appearing on
// left-hand side of an assignment) to "names".
// The "value" in the hashtable will be the type of the variable.
// (Both key and value will be shared with the AST, so don't need to be freed.)
//
// Note: This will "dereference" any refs declared inside the block, e.g.
// "ref r = x; r = 10" will be recorded as a modification to x, rather than r.
// However, "pre-existing" refs will not be tracked in this way. If this is
// a concern, use get_modified_vars_deref (in verifier_context.c) instead.
//
void get_modified_var_names(struct HashTable *names, struct Statement *stmt);

#endif
