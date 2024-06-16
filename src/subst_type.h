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

// These functions both return a newly allocated Type (any relevant
// parts of the input are copied as needed).

struct Type * substitute_in_type_from_list(struct TyVarList *tyvars,
                                           struct TypeList *tyargs,
                                           const struct Type *type);

// theta should be a map from tyvar name to struct Type *.
struct Type * substitute_in_type_from_hashtable(struct HashTable *theta,
                                                const struct Type *type);

#endif
