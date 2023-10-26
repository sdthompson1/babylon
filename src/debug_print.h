/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef DEBUG_PRINT_H
#define DEBUG_PRINT_H

#include <stdio.h>

struct Module;

void print_module(FILE *file, struct Module *module);

#endif
