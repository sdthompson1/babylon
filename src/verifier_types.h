/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_TYPES_H
#define VERIFIER_TYPES_H

struct Sexpr;

// Converts type to Sexpr form. Never fails.
struct Sexpr * verify_type(struct Type *type);

// Converts a NameTypeList to a list of types, ignoring the names
struct Sexpr * verify_name_type_list(struct NameTypeList *type_list);

#endif
