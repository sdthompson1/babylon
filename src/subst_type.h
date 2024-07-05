/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef SUBST_TYPE_H
#define SUBST_TYPE_H

struct HashTable;
struct Type;
struct TypeList;
struct TyVarList;


// Two functions to substitute in a Type. These return a newly
// allocated Type (any relevant parts of the input are copied as
// needed).

// In substitute_in_type_from_hashtable, theta should be a map from
// tyvar name to struct Type *.

// Restrictions: The input type must not contain TY_FORALL or
// TY_LAMBDA.

struct Type * substitute_in_type_from_list(struct TyVarList *tyvars,
                                           struct TypeList *tyargs,
                                           const struct Type *type);

struct Type * substitute_in_type_from_hashtable(struct HashTable *theta,
                                                const struct Type *type);



// Function to substitute all types in a DeclGroup (and all "next"
// DeclGroups), in place.

// This is a different implementation to the above, and this time it
// can cope with TY_FORALL or TY_LAMBDA types (doing proper capture
// avoiding substitution). The limitations are that it can NOT handle
// TY_UNIVAR, and it can only substitute a single variable at a time.

void substitute_type_in_decl_group(const char *tyvar_name,
                                   struct Type *replacement,
                                   struct DeclGroup *group);

#endif
