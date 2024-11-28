/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

// This file contains some useful wrapper functions around the TOML C
// library.

#ifndef TOML_EXT_H
#define TOML_EXT_H

#include "toml.h"

// Replacement for toml_table_array that prints an error (as well as
// returning NULL) if the value is present but not actually an array.
toml_array_t* toml_table_array_ext(const char *filename,
                                   const toml_table_t *table,
                                   const char *key,
                                   bool *error);

// Read a list of strings
struct NameList *read_toml_string_list(const char *filename,
                                       const toml_array_t *array,
                                       bool *error);

// Reads a string from a toml table. Returns newly allocated string.
// If key not present, or not a string:
//   - if 'dflt' is NULL, prints error and returns NULL;
//   - otherwise, returns a copy of dflt.
// 'filename' is for error messages.
char* read_toml_string(const char *filename,
                       const toml_table_t *table,
                       const char *key,
                       const char *dflt);

#endif
