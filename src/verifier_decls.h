/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_DECLS_H
#define VERIFIER_DECLS_H

#include <stdbool.h>

struct Decl;
struct VContext;

bool verify_decl_group(struct VContext *context, struct Decl *decl_group);

#endif
