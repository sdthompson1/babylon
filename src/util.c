/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "util.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

char* copy_string(const char *str)
{
    char* result = alloc(strlen(str) + 1);
    strcpy(result, str);
    return result;
}

char* copy_string_2(const char *str1, const char *str2)
{
    size_t len1 = strlen(str1);
    size_t len2 = strlen(str2);
    char *result = alloc(len1 + len2 + 1);
    strcpy(result, str1);
    strcpy(result + len1, str2);
    return result;
}

char* copy_string_3(const char *str1, const char *str2, const char *str3)
{
    size_t len1 = strlen(str1);
    size_t len2 = strlen(str2);
    size_t len3 = strlen(str3);
    char* result = alloc(len1 + len2 + len3 + 1);
    strcpy(result, str1);
    strcpy(result + len1, str2);
    strcpy(result + len1 + len2, str3);
    return result;
}

/*
char* copy_string_4(const char *str1, const char *str2, const char *str3, const char *str4)
{
    size_t len1 = strlen(str1);
    size_t len2 = strlen(str2);
    size_t len3 = strlen(str3);
    size_t len4 = strlen(str4);
    char* result = alloc(len1 + len2 + len3 + len4 + 1);
    strcpy(result, str1);
    strcpy(result + len1, str2);
    strcpy(result + len1 + len2, str3);
    strcpy(result + len1 + len2 + len3, str4);
    return result;
}
*/

struct NameList * copy_name_list(struct NameList *list)
{
    struct NameList *result = NULL;
    struct NameList **tail = &result;
    while (list) {
        struct NameList *node = alloc(sizeof(struct NameList));
        node->name = copy_string(list->name);
        node->next = NULL;
        *tail = node;
        tail = &node->next;
        list = list->next;
    }
    return result;
}

static struct NameList *sort_name_list_and_append(struct NameList *list,
                                                  struct NameList *to_append)
{
    // Simple quicksort implementation.

    // This has worst case O(n^2) performance, but should be O(n*log n) on
    // average. We don't anticipate the namelists being all that long though,
    // so hopefully the worst case performance won't be an issue.

    // Base case: empty list.
    if (list == NULL) {
        return to_append;
    }

    // Break off the first element to act as pivot
    struct NameList *pivot = list;
    list = pivot->next;
    pivot->next = NULL;

    // Create empty "lower" and "upper" lists
    struct NameList *lower = NULL;
    struct NameList *upper = NULL;

    // Repeatedly take one element from 'list' and add it to 'lower'
    // if it is less than pivot, or 'upper' if it is greater than or
    // equal to pivot.
    while (list) {
        struct NameList *list_next = list->next;
        if (strcmp(list->name, pivot->name) < 0) {
            list->next = lower;
            lower = list;
        } else {
            list->next = upper;
            upper = list;
        }
        list = list_next;
    }

    // We want to return sort(lower) ++ pivot ++ sort(upper) ++ to_append.
    upper = sort_name_list_and_append(upper, to_append);
    pivot->next = upper;
    lower = sort_name_list_and_append(lower, pivot);
    return lower;
}

struct NameList *sort_name_list(struct NameList *list)
{
    return sort_name_list_and_append(list, NULL);
}

void free_name_list(struct NameList *list)
{
    while (list) {
        struct NameList *next = list->next;
        free((char*)list->name);
        free(list);
        list = next;
    }
}


// Little-endian read/write helpers

// Hopefully the compiler will do a reasonable job of optimising
// these. GCC seems able to.

uint16_t read_u16(const uint8_t *ptr)
{
    return (uint16_t)ptr[0]
        | ((uint16_t)ptr[1] << 8);
}

int16_t read_i16(const uint8_t *ptr)
{
    uint16_t x = read_u16(ptr);
    return *(int16_t*)&x;
}

void write_u16(uint8_t *ptr, uint16_t value)
{
    ptr[0] = value;
    ptr[1] = value >> 8u;
}

uint32_t read_u32(const uint8_t *ptr)
{
    return (uint32_t)ptr[0]
        | ((uint32_t)ptr[1] << 8)
        | ((uint32_t)ptr[2] << 16)
        | ((uint32_t)ptr[3] << 24);
}

int32_t read_i32(const uint8_t *ptr)
{
    uint32_t x = read_u32(ptr);
    return *(int32_t*)&x;
}

void write_u32(uint8_t *ptr, uint32_t value)
{
    ptr[0] = value;
    ptr[1] = value >> 8u;
    ptr[2] = value >> 16u;
    ptr[3] = value >> 24u;
}

uint64_t read_u64(const uint8_t *ptr)
{
    return (uint64_t)ptr[0]
        | ((uint64_t)ptr[1] << 8)
        | ((uint64_t)ptr[2] << 16)
        | ((uint64_t)ptr[3] << 24)
        | ((uint64_t)ptr[4] << 32)
        | ((uint64_t)ptr[5] << 40)
        | ((uint64_t)ptr[6] << 48)
        | ((uint64_t)ptr[7] << 56);
}

int64_t read_i64(const uint8_t *ptr)
{
    uint64_t x = read_u64(ptr);
    return *(int64_t*)&x;
}

void write_u64(uint8_t *ptr, uint64_t value)
{
    ptr[0] = value;
    ptr[1] = value >> 8u;
    ptr[2] = value >> 16u;
    ptr[3] = value >> 24u;
    ptr[4] = value >> 32u;
    ptr[5] = value >> 40u;
    ptr[6] = value >> 48u;
    ptr[7] = value >> 56u;
}
