/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"

#include <stdlib.h>

void *alloc(size_t num_bytes)
{
    void *result = malloc(num_bytes);
    if (result == NULL) {
        fatal_error("malloc call failed");
    }
    return result;
}
