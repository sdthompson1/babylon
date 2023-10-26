/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



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
