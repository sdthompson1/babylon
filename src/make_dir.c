/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "make_dir.h"

#include <errno.h>
#include <sys/stat.h>

bool maybe_mkdir(const char *path, mode_t mode)
{
    errno = 0;

    // Try to make the directory.
    if (mkdir(path, mode) == 0) {
        // Success.
        return true;
    }

    if (errno != EEXIST) {
        // Failed for some reason other than EEXIST.
        return false;
    }

    struct stat st;
    if (stat(path, &st) != 0) {
        // Failed to stat the existing thing.
        return false;
    }

    if (!S_ISDIR(st.st_mode)) {
        // There is an existing thing (not a directory) blocking the directory creation.
        return false;
    }

    // The directory already exists so we are OK.
    return true;
}
