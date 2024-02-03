/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef CACHE_DB_H
#define CACHE_DB_H

// Functions for working with babylon.cache.

#include "sha256.h"
#include <stdbool.h>

struct CacheDb;

// Attempt to open file at prefix + "babylon.cache".
// If fails, prints a warning message and returns NULL.
struct CacheDb * open_cache_db(const char *prefix);

// Close/free a CacheDb.
void close_cache_db(struct CacheDb *db);

// Determine whether a particular SHA256 hash (represented as a binary blob)
// exists in the database.
// (It is safe to call this with db==NULL, it will return false in that case.)
bool sha256_exists_in_db(struct CacheDb *db, const uint8_t hash[SHA256_HASH_LENGTH]);

// Insert a hash into the database.
// (It is safe to call this with db==NULL, it will do nothing in that case.)
void add_sha256_to_db(struct CacheDb *db, const uint8_t hash[SHA256_HASH_LENGTH]);

#endif
