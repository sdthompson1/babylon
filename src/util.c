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

char * copy_string_5(const char *str1, const char *str2, const char *str3, const char *str4,
                     const char *str5)
{
    size_t len1 = strlen(str1);
    size_t len2 = strlen(str2);
    size_t len3 = strlen(str3);
    size_t len4 = strlen(str4);
    size_t len5 = strlen(str5);
    char* result = alloc(len1 + len2 + len3 + len4 + len5 + 1);
    strcpy(result, str1);
    strcpy(result + len1, str2);
    strcpy(result + len1 + len2, str3);
    strcpy(result + len1 + len2 + len3, str4);
    strcpy(result + len1 + len2 + len3 + len4, str5);
    return result;
}

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
