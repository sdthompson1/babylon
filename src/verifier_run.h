/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef VERIFIER_RUN_H
#define VERIFIER_RUN_H

#include "location.h"

struct Sexpr;
struct VContext;

// Verify the condition given by FOL-expression "condition".
// The commands listed in "asserts" are added to the FOL-program.
// Also the definitions of any symbols mentioned in "asserts" or "condition" are looked
// up in "env", and those definitions are added to the FOL-program as well.

// Note: if context->interface_only is true, the check is skipped.

void verify_condition(struct VContext *context,
                      struct Location location,
                      struct Sexpr *condition,    // NOT handed over
                      const char *description,    // NOT handed over
                      const char *error_msg);     // handover

#endif
