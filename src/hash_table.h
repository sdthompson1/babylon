/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef HASH_TABLE_H
#define HASH_TABLE_H

#include <stdbool.h>
#include <stddef.h>

struct HashTable;
struct HashIterator;


// Construction, destruction
struct HashTable * new_hash_table();
void free_hash_table(struct HashTable *table);

// Swap two hash tables quickly
void hash_table_swap(struct HashTable *table1, struct HashTable *table2);


// Insertion, removal
// Note: keys and values are not copied; they are stored in the table as pointers.
// For insert, if key already exists, the 'value' is overwritten (but the 'key' stored
// in the table is unchanged).
// For remove, if key doesn't exist, the table is unchanged.
void hash_table_insert(struct HashTable *table, const char *key, void *value);
void hash_table_remove(struct HashTable *table, const char *key);


// Lookup
bool hash_table_contains_key(const struct HashTable *table, const char *key);
void *hash_table_lookup(const struct HashTable *table, const char *key);
void hash_table_lookup_2(const struct HashTable *table, const char *key, const char **key_out, void **value_out);

// Check if empty; get size; clear
bool hash_table_empty(const struct HashTable *table);
size_t hash_table_size(const struct HashTable *table);
void hash_table_clear(struct HashTable *table);


// Iterators
// hash_iterator_next returns true if an item was found, or false if we reached the end.
// It is valid for 'key' or 'value' (or both) to be NULL.
// Note: do not insert/remove new items while iterating (but modifying existing items is fine).
// Note: after reaching the end, a new iteration (from the beginning) may be started
// by calling hash_iterator_next again.
struct HashIterator * new_hash_iterator(struct HashTable *table);
void free_hash_iterator(struct HashIterator *iterator);
bool hash_iterator_next(struct HashIterator *iterator, const char **key, void **value);
void hash_iterator_write_value(struct HashIterator *iterator, void *new_value);


// "Head" operations
void hash_table_get_first(const struct HashTable *table, const char **key, void **value);
void hash_table_remove_first(struct HashTable *table);


// Run a function on all keys and values in the table
void hash_table_for_each(struct HashTable *table,
                         void (*func)(void *context, const char *key, void *value),
                         void *context);

// Helpers that might be useful with hash_table_for_each. These call
// "free" on the key, value or both. ("context" is ignored and can be
// set to NULL for these.)
void ht_free_key(void *context, const char *key, void *value);
void ht_free_value(void *context, const char *key, void *value);
void ht_free_key_and_value(void *context, const char *key, void *value);

#endif
