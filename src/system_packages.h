/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef SYSTEM_PACKAGES_H
#define SYSTEM_PACKAGES_H

#include "dep_list.h"
#include "util.h"

// On success, these return true and populate 'output'.

// On failure, print error message(s), return false, leave 'output' unchanged.

bool system_package_cflags(const char *pkg_config_cmd,
                           struct DepList *packages,
                           struct NameList **output);

bool system_package_libs(const char *pkg_config_cmd,
                         struct DepList *packages,
                         struct NameList **output);

#endif
