/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "alloc.h"
#include "cprint.h"
#include "error.h"
#include "stringbuf.h"

#include <stdlib.h>
#include <string.h>

struct CPrinter {
    FILE *file;
    struct StringBuf *buf;
    size_t cur_buf;
    int indent;
    int *column;
    size_t num_allocated;
};

#define MAX_COLUMN 70
#define INDENT "    "

static void expand_c_printer(struct CPrinter *pr)
{
    size_t old_num_alloc = pr->num_allocated;
    size_t new_num_alloc = old_num_alloc * 2;
    if (new_num_alloc < 5) {
        new_num_alloc = 5;
    }
    struct StringBuf *new_buf = alloc(sizeof(struct StringBuf) * new_num_alloc);
    int *new_column = alloc(sizeof(int) * (new_num_alloc + 1));
    if (old_num_alloc > 0) {
        new_column[0] = pr->column[0];
    }
    for (size_t i = 0; i < old_num_alloc; ++i) {
        new_column[i+1] = pr->column[i+1];
        new_buf[i] = pr->buf[i];
    }
    for (size_t i = old_num_alloc; i < new_num_alloc; ++i) {
        stringbuf_init(&new_buf[i]);
        new_column[i] = 0;
    }
    free(pr->buf);
    free(pr->column);
    pr->buf = new_buf;
    pr->column = new_column;
    pr->num_allocated = new_num_alloc;
}

struct CPrinter * new_c_printer(FILE *output_file)
{
    struct CPrinter * pr = alloc(sizeof(struct CPrinter));
    pr->file = output_file;
    pr->buf = NULL;
    pr->cur_buf = 0;
    pr->indent = 0;
    pr->column = NULL;
    pr->num_allocated = 0;
    expand_c_printer(pr);
    return pr;
}

void free_c_printer(struct CPrinter *pr)
{
    if (pr->cur_buf != 0) {
        fatal_error("free_c_printer: unbalanced begin/end item");
    }
    for (size_t i = 0; i < pr->num_allocated; ++i) {
        stringbuf_free(&pr->buf[i]);
    }
    free(pr->buf);
    free(pr->column);
    free(pr);
}

static void output(struct CPrinter *pr, const char *str)
{
    pr->column[pr->cur_buf] += strlen(str);
    if (pr->cur_buf == 0) {
        fprintf(pr->file, "%s", str);
    } else {
        stringbuf_append(&pr->buf[pr->cur_buf - 1], str);
    }
}

void print_token(struct CPrinter *pr, const char *token)
{
    int extra_indent = 0;
    if (pr->column[pr->cur_buf] > MAX_COLUMN) {
        new_line(pr);
        extra_indent = 1;
    }
    if (pr->column[pr->cur_buf] == 0) {
        for (int i = 0; i < pr->indent + extra_indent; ++i) {
            output(pr, INDENT);
        }
    } else {
        if (token[0] != ';' && token[0] != ',') {
            output(pr, " ");
        }
    }
    output(pr, token);
}

void new_line(struct CPrinter *pr)
{
    output(pr, "\n");
    pr->column[pr->cur_buf] = 0;
}

void increase_indent(struct CPrinter *pr)
{
    pr->indent++;
}

void decrease_indent(struct CPrinter *pr)
{
    pr->indent--;
    if (pr->indent < 0) {
        fatal_error("indent negative");
    }
}

void begin_item(struct CPrinter *pr)
{
    pr->cur_buf++;
    if (pr->cur_buf == pr->num_allocated) {
        expand_c_printer(pr);
    }
}

void end_item(struct CPrinter *pr)
{
    if (pr->cur_buf == 0) {
        fatal_error("illegal end_item");
    }
    if (pr->buf[pr->cur_buf - 1].data) {
        fprintf(pr->file, "%s", pr->buf[pr->cur_buf - 1].data);
        stringbuf_clear(&pr->buf[pr->cur_buf - 1]);
    }
    pr->cur_buf--;
}
