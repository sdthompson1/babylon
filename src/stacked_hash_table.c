/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "stacked_hash_table.h"

bool stacked_hash_table_contains_key(const struct StackedHashTable *stack, const char *key)
{
    while (stack != NULL) {
        if (hash_table_contains_key(stack->table, key)) {
            return true;
        }
        stack = stack->base;
    }
    return false;
}

void * stacked_hash_table_lookup(const struct StackedHashTable *stack, const char *key)
{
    const char *key_out;
    void *value_out;
    stacked_hash_table_lookup_2(stack, key, &key_out, &value_out);
    return value_out;
}

void stacked_hash_table_lookup_2(const struct StackedHashTable *stack, const char *key, const char **key_out, void **value_out)
{
    const char *found_key;
    while (stack != NULL) {
        hash_table_lookup_2(stack->table, key, &found_key, value_out);
        if (found_key != NULL) {
            // Found it.
            if (key_out) {
                *key_out = found_key;
            }
            return;
        }
        stack = stack->base;
    }
    // Not found in any table.
    if (key_out) {
        *key_out = NULL;
    }
    if (value_out) {
        *value_out = NULL;
    }
}

void stacked_hash_table_collapse(struct StackedHashTable *stack,
                                 void *context,
                                 void (*dtor)(void *context, const char *key, void *value))
{
    struct HashIterator *iter = new_hash_iterator(stack->table);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        const char *old_key;
        void *old_value;
        hash_table_lookup_2(stack->base->table, key, &old_key, &old_value);
        if (old_key) {
            hash_table_remove(stack->base->table, old_key);
            if (dtor) {
                (*dtor)(context, old_key, old_value);
            }
        }
        hash_table_insert(stack->base->table, key, value);
    }
    free_hash_iterator(iter);
    hash_table_clear(stack->table);
}
