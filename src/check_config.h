/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef CHECK_CONFIG_H
#define CHECK_CONFIG_H

#include <stdbool.h>

struct CompilerConfig;

bool check_config(struct CompilerConfig *config);

#endif
