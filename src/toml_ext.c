/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "alloc.h"
#include "toml_ext.h"
#include "util.h"

#include <string.h>

toml_array_t* toml_table_array_ext(const char *filename,
                                   const toml_table_t *table,
                                   const char *key,
                                   bool *error)
{
    if (error) *error = false;

    toml_array_t * arr = toml_table_array(table, key);
    if (arr != NULL) {
        return arr;
    }

    // toml_table_array returns NULL if either the key is not found
    // or the key has non-array type. We have to figure out which it is.
    int len = toml_table_len(table);
    for (int i = 0; i < len; ++i) {
        int keylen;
        if (strcmp(toml_table_key(table, i, &keylen), key) == 0) {
            // Found the key as a non-array key
            fprintf(stderr, "%s: '%s' has incorrect type (should be array)\n", filename, key);
            if (error) *error = true;
            break;
        }
    }

    // Either way, we return NULL
    return NULL;
}

struct NameList *read_toml_string_list(const char *filename,
                                       const toml_array_t *array,
                                       bool *error)
{
    struct NameList *result = NULL;
    struct NameList **tail = &result;
    *error = false;

    int len = toml_array_len(array);
    for (int i = 0; i < len; ++i) {
        toml_value_t str = toml_array_string(array, i);
        if (str.ok) {
            struct NameList *node = alloc(sizeof(struct NameList));
            node->name = str.u.s;
            node->next = NULL;
            *tail = node;
            tail = &node->next;
        } else {
            fprintf(stderr, "%s: invalid string found in array\n", filename);
            *error = true;
            free_name_list(result);
            return NULL;
        }
    }

    return result;
}

char* read_toml_string(const char *filename,
                       const toml_table_t *table,
                       const char *key,
                       const char *dflt)
{
    toml_value_t val = toml_table_string(table, key);
    if (val.ok) {
        return val.u.s;  // caller must free this
    } else if (dflt) {
        return copy_string(dflt);
    } else {
        fprintf(stderr, "%s: '%s' missing or invalid\n", filename, key);
        return NULL;
    }
}
