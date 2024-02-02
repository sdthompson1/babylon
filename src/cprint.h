/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef CPRINT_H
#define CPRINT_H

#include <stdio.h>

struct CPrinter;

struct CPrinter * new_c_printer(FILE *output_file);
void free_c_printer(struct CPrinter *pr);

void print_token(struct CPrinter *pr, const char *token);

void new_line(struct CPrinter *pr);
void increase_indent(struct CPrinter *pr);
void decrease_indent(struct CPrinter *pr);

// An "Item" will be held back and only printed when end_item is called.
// Items can be nested, in which case the "inner" items will appear before
// the "outer" ones in the output.
void begin_item(struct CPrinter *pr);
void end_item(struct CPrinter *pr);

#endif
