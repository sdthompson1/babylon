/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef ASM_CHECK_STACK_H
#define ASM_CHECK_STACK_H

// Defines the "rts_check_stack" function.

#include <stdint.h>

struct AsmGen;
void make_check_stack_function(struct AsmGen *gen, uint64_t *label_num);

#endif
