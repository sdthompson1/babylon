/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "location.h"

#include <stdio.h>
#include <string.h>

struct Location g_no_location = { NULL, 0, 0, 0, 0 };

void format_location(const struct Location *loc,
                     bool include_end,
                     bool include_slash,
                     char *buf, int len)
{
    if (loc->filename == NULL && loc->begin_line_num == 0) {
        if (len > 0) buf[0] = 0;
        return;
    }

    const char *file = loc->filename;
    if (file == NULL) file = "(no file)";

    if (!include_slash) {
        const char *last_slash = strrchr(file, '/');
        if (last_slash) {
            file = last_slash + 1;
        }
    }

    if (loc->begin_line_num != 0) {
        if (include_end) {
            if (loc->end_line_num == loc->begin_line_num) {
                snprintf(buf, len, "%s:%d:%d-%d", file,
                         loc->begin_line_num,
                         loc->begin_column_num,
                         loc->end_column_num);
            } else {
                snprintf(buf, len, "%s:%d:%d-%d:%d", file,
                         loc->begin_line_num,
                         loc->begin_column_num,
                         loc->end_line_num,
                         loc->end_column_num);
            }
        } else {
            snprintf(buf, len, "%s:%d:%d", file,
                     loc->begin_line_num,
                     loc->begin_column_num);
        }
    } else {
        snprintf(buf, len, "%s", file);
    }
}

void set_location_end(struct Location *loc, const struct Location *from)
{
    loc->end_line_num = from->end_line_num;
    loc->end_column_num = from->end_column_num;
}

struct Location * shallow_copy_location(struct Location *loc)
{
    struct Location * result = alloc(sizeof(struct Location));
    memcpy(result, loc, sizeof(struct Location));
    return result;
}
