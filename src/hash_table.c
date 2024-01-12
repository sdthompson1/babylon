/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"
#include "hash_table.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>


#define INITIAL_CAPACITY 16


struct HashItem {
    const char *key;
    void *value;
    struct HashItem *prev;
    struct HashItem *next;
};

struct HashTable {
    size_t size;
    size_t capacity;

    // double linked list of all occupied HashItems
    struct HashItem * first;

    // the table itself (array of length 'capacity', or NULL)
    struct HashItem * items;
};


static size_t hash(const char *key)
{
    size_t hash = 5381u;
    char c;

    while ((c = *key++) != 0) {
        hash = ((hash << 5u) + hash) ^ (size_t)c;
    }

    return hash;
}

static struct HashItem *find_item(const struct HashTable *table, const char *key)
{
    size_t i = hash(key) % table->capacity;

    while (true) {
        if (table->items[i].key == NULL
            || strcmp(table->items[i].key, key) == 0) {
                return &table->items[i];
        }

        i = i + 1;
        if (i == table->capacity) {
            i = 0;
        }
    }
}

static void resize_table(struct HashTable *table, size_t new_capacity)
{
    if (new_capacity == 0) {
        fatal_error("resize_table: new_capacity is zero");
    }

    // this is unlikely, but it doesn't hurt to check:
    if (new_capacity > SIZE_MAX / sizeof(struct HashItem)) {
        fatal_error("resize_table: new_capacity is too big");
    }

    struct HashItem *old_first = table->first;
    struct HashItem *old_items = table->items;

    table->size = 0;
    table->capacity = new_capacity;
    table->first = NULL;

    size_t num_bytes = new_capacity * sizeof(struct HashItem);
    table->items = alloc(num_bytes);
    memset(table->items, 0, num_bytes);

    if (old_first != NULL) {
        for (struct HashItem *item = old_first; item; item = item->next) {
            hash_table_insert(table, item->key, item->value);
        }
    }

    free(old_items);
}

struct HashTable * new_hash_table()
{
    struct HashTable * result = alloc(sizeof(struct HashTable));

    result->size = 0;
    result->capacity = 0;
    result->first = NULL;
    result->items = NULL;

    return result;
}

void free_hash_table(struct HashTable *table)
{
    if (table) {
        free(table->items);
        free(table);
    }
}

void hash_table_swap(struct HashTable *table1, struct HashTable *table2)
{
    // we can just "memcpy" the struct contents
    struct HashTable tmp = *table2;
    *table2 = *table1;
    *table1 = tmp;
}

static void copy_helper(void *context, const char *key, void *value)
{
    hash_table_insert(context, key, value);
}

void hash_table_copy(struct HashTable *dest, struct HashTable *src)
{
    hash_table_clear(dest);
    hash_table_for_each(src, copy_helper, dest);
}

void hash_table_insert(struct HashTable *table, const char *key, void *value)
{
    // Rehash when load factor is around 0.6, i.e.
    // size >= 3/5*capacity, or 5*size >= 3*capacity.

    if (5 * table->size >= 3 * table->capacity) {
        if (table->capacity == 0) {
            resize_table(table, INITIAL_CAPACITY);
        } else {
            resize_table(table, table->capacity * 2);
        }
    }

    struct HashItem *item = find_item(table, key);

    if (item->key) {
        // overwrite existing item
        item->value = value;

    } else {
        // insert new item
        table->size ++;
        item->key = key;
        item->value = value;
        item->prev = NULL;
        item->next = table->first;

        if (table->first != NULL) {
            table->first->prev = item;
        }
        table->first = item;
    }
}

void hash_table_remove(struct HashTable *table, const char *key)
{
    if (table->size == 0) {
        return;
    }

    struct HashItem *item = find_item(table, key);
    if (item->key == NULL) {
        return;
    }

    size_t i = item - table->items;
    size_t j = i + 1;
    if (j == table->capacity) {
        j = 0;
    }

    while (true) {
        if (table->items[j].key == NULL) {

            table->items[i].key = NULL;
            table->items[i].value = NULL;

            if (table->items[i].next) {
                table->items[i].next->prev = table->items[i].prev;
            }
            if (table->items[i].prev) {
                table->items[i].prev->next = table->items[i].next;
            } else {
                table->first = table->items[i].next;
            }

            table->items[i].next = NULL;
            table->items[i].prev = NULL;

            table->size --;

            // Note: currently table capacity isn't reduced on deletions.

            return;
        }

        size_t k = hash(table->items[j].key) % table->capacity;
        if ((j > i && (k <= i || k > j)) ||
            (j < i && (k <= i && k > j))) {

            table->items[i].key = table->items[j].key;
            table->items[i].value = table->items[j].value;

            i = j;
        }

        j = j + 1;
        if (j == table->capacity) {
            j = 0;
        }
    }
}

bool hash_table_contains_key(const struct HashTable *table, const char *key)
{
    if (table->size == 0) {
        return false;
    }

    return find_item(table, key)->key != NULL;
}

void *hash_table_lookup(const struct HashTable *table, const char *key)
{
    if (table->size == 0) {
        return NULL;
    }

    return find_item(table, key)->value;
}

void hash_table_lookup_2(const struct HashTable *table, const char *key, const char **key_out, void **value_out)
{
    if (table->size == 0) {
        if (key_out) {
            *key_out = NULL;
        }
        if (value_out) {
            *value_out = NULL;
        }
    } else {
        struct HashItem *item = find_item(table, key);
        if (key_out) {
            *key_out = item->key;
        }
        if (value_out) {
            *value_out = item->value;
        }
    }
}

bool hash_table_empty(const struct HashTable *table)
{
    return table->size == 0;
}

size_t hash_table_size(const struct HashTable *table)
{
    return table->size;
}

void hash_table_clear(struct HashTable *table)
{
    struct HashItem *item = table->first;
    while (item) {
        struct HashItem *next = item->next;
        item->key = NULL;
        item->value = NULL;
        item->prev = NULL;
        item->next = NULL;
        item = next;
    }

    table->size = 0;
    table->first = NULL;
}


struct HashIterator {
    struct HashTable *table;
    struct HashItem *item;
};

struct HashIterator * new_hash_iterator(struct HashTable *table)
{
    struct HashIterator *iterator = alloc(sizeof(struct HashIterator));
    iterator->table = table;
    iterator->item = NULL;
    return iterator;
}

void free_hash_iterator(struct HashIterator *iterator)
{
    free(iterator);
}

bool hash_iterator_next(struct HashIterator *iterator, const char **key, void **value)
{
    if (iterator->item == NULL) {
        iterator->item = iterator->table->first;
    } else {
        iterator->item = iterator->item->next;
    }

    if (iterator->item == NULL) {
        return false;
    }

    if (key) {
        *key = iterator->item->key;
    }
    if (value) {
        *value = iterator->item->value;
    }

    return true;
}

void hash_iterator_write_value(struct HashIterator *iterator, void *new_value)
{
    iterator->item->value = new_value;
}

void hash_table_get_first(const struct HashTable *table, const char **key, void **value)
{
    if (table->first) {
        *key = table->first->key;
        *value = table->first->value;
    } else {
        *key = NULL;
        *value = NULL;
    }
}

void hash_table_remove_first(struct HashTable *table)
{
    if (table->first) {
        hash_table_remove(table, table->first->key);
    }
}

void hash_table_for_each(struct HashTable *table, void (*func)(void *context, const char *key, void *value), void *context)
{
    struct HashIterator * iter = new_hash_iterator(table);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        (*func)(context, key, value);
    }
    free_hash_iterator(iter);
}

void ht_free_key(void *context, const char *key, void *value)
{
    free((char*)key);
}

void ht_free_value(void *context, const char *key, void *value)
{
    free(value);
}

void ht_free_key_and_value(void *context, const char *key, void *value)
{
    free((char*)key);
    free(value);
}
