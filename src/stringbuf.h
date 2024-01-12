/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef STRINGBUF_H
#define STRINGBUF_H

#include <stddef.h>

// Simple string "class".

struct StringBuf {
    // invariants:
    //   capacity == 0 ==> length == 0
    //   capacity == 0 ==> data == NULL
    //   capacity != 0 ==> length < capacity
    //   capacity != 0 ==> data points to a malloc-allocated array of length capacity
    //   capacity != 0 ==> data[length] = 0
    //   capacity != 0 ==> forall i < length. data[i] != 0
    size_t length;
    size_t capacity;
    char *data;
};

void stringbuf_init(struct StringBuf *buf);
void stringbuf_free(struct StringBuf *buf);
void stringbuf_append(struct StringBuf *buf, const char *str);
void stringbuf_printf(struct StringBuf *buf, const char *format, ...);  // append formatted string
void stringbuf_clear(struct StringBuf *buf);

#endif
