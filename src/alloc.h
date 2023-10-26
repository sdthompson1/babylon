/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef ALLOC_H
#define ALLOC_H

#include <stddef.h>

// Simple wrapper for malloc which calls stop_with_out_of_memory() if
// malloc ever returns NULL.
void *alloc(size_t num_bytes);

#endif
