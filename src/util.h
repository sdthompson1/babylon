/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef UTIL_H
#define UTIL_H

#include <stdint.h>

struct NameList {
    const char *name;
    struct NameList *next;
};

// Note: the input strings cannot be NULL for the copy_string functions
char * copy_string(const char *input);
char * copy_string_2(const char *str1, const char *str2);
char * copy_string_3(const char *str1, const char *str2, const char *str3);
char * copy_string_4(const char *str1, const char *str2, const char *str3, const char *str4);
char * copy_string_5(const char *str1, const char *str2, const char *str3, const char *str4,
                     const char *str5);


struct NameList * copy_name_list(struct NameList *list);

// sort a NameList in place. returns new head pointer.
struct NameList * sort_name_list(struct NameList *list);

// free an entire NameList, also freeing the name pointers.
void free_name_list(struct NameList *list);



#endif
