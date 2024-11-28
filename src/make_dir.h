/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef MAKE_DIR_H
#define MAKE_DIR_H

#include <stdbool.h>
#include <sys/types.h>

// If 'path' does not already exist as a directory, then create it.
// Returns true on success (or if the dir already exists).
// Returns false if the dir doesn't exist and couldn't be created.
bool maybe_mkdir(const char *path, mode_t mode);

#endif
