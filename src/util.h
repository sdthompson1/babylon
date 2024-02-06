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
//char * copy_string_4(const char *str1, const char *str2, const char *str3, const char *str4);


struct NameList * copy_name_list(struct NameList *list);

// sort a NameList in place. returns new head pointer.
struct NameList * sort_name_list(struct NameList *list);

// free an entire NameList, also freeing the name pointers.
void free_name_list(struct NameList *list);


// Little-endian memory read/write functions
uint16_t read_u16(const uint8_t *ptr);
int16_t read_i16(const uint8_t *ptr);
void write_u16(uint8_t *ptr, uint16_t value);
uint32_t read_u32(const uint8_t *ptr);
int32_t read_i32(const uint8_t *ptr);
void write_u32(uint8_t *ptr, uint32_t value);
uint64_t read_u64(const uint8_t *ptr);
int64_t read_i64(const uint8_t *ptr);
void write_u64(uint8_t *ptr, uint64_t value);


#define GUARD_PAGE_SIZE 4096


#endif
