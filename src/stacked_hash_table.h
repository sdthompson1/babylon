/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef STACKED_HASH_TABLE_H
#define STACKED_HASH_TABLE_H

#include "hash_table.h"

struct StackedHashTable {
    struct HashTable *table;  // must be non-NULL to be valid
    struct StackedHashTable *base;   // can be NULL
};

bool stacked_hash_table_contains_key(const struct StackedHashTable *stack, const char *key);
void *stacked_hash_table_lookup(const struct StackedHashTable *stack, const char *key);
void stacked_hash_table_lookup_2(const struct StackedHashTable *stack, const char *key, const char **key_out, void **value_out);

// This empties the top level table, and moves all the keys to the next level below.
// Any existing keys on the level below are replaced; the given destructor function is
// called on them first.
void stacked_hash_table_collapse(struct StackedHashTable *stack,
                                 void *context,
                                 void (*dtor)(void *context, const char *key, void *value));

#endif
