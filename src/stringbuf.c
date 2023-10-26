/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "stringbuf.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void stringbuf_init(struct StringBuf *buf)
{
    buf->length = 0;
    buf->capacity = 0;
    buf->data = NULL;
}

void stringbuf_free(struct StringBuf *buf)
{
    buf->length = 0;
    buf->capacity = 0;
    free(buf->data);
    buf->data = NULL;
}

// expects new_capacity > capacity
static void stringbuf_realloc(struct StringBuf *buf, size_t new_capacity)
{
    char *new_data = alloc(new_capacity);
    if (buf->data) {
        strcpy(new_data, buf->data);
        free(buf->data);
    }
    buf->data = new_data;
    buf->capacity = new_capacity;
}

// ensure capacity >= new_len + 1
static void ensure_capacity(struct StringBuf *buf, size_t new_len)
{
    if (new_len >= buf->capacity) {
        size_t new_capacity = buf->capacity * 2;
        if (new_len >= new_capacity) {
            new_capacity = new_len + 1;
        }
        stringbuf_realloc(buf, new_capacity);
    }
}

void stringbuf_append(struct StringBuf *buf, const char *str)
{
    size_t incoming_len = strlen(str);
    size_t new_len = buf->length + incoming_len;
    ensure_capacity(buf, new_len);
    strcpy(&buf->data[buf->length], str);
    buf->length = new_len;
}

void stringbuf_printf(struct StringBuf *buf, const char *format, ...)
{
    va_list args;

    va_start(args, format);
    // len does NOT include the null terminator
    int len = vsnprintf(NULL, 0, format, args);
    va_end(args);

    if (len < 0) {
        return;
    }

    size_t new_len = buf->length + len;
    size_t new_capacity = new_len + 1;   // +1 for null terminator
    ensure_capacity(buf, new_capacity);

    va_start(args, format);
    vsnprintf(&buf->data[buf->length], new_capacity - buf->length, format, args);
    va_end(args);

    buf->length = new_len;
}

void stringbuf_clear(struct StringBuf *buf)
{
    if (buf->length != 0) {
        buf->length = 0;
        buf->data[0] = 0;
    }
}
