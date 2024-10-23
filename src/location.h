/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef LOCATION_H
#define LOCATION_H

#include <stdbool.h>

struct Location {
    // Note: the 'filename' is NOT typically allocated with malloc;
    // the same filename ptr is often shared between several different
    // objects.
    const char *filename;
    int begin_line_num;
    int begin_column_num;
    int end_line_num;
    int end_column_num;
};

extern struct Location g_no_location;

void format_location(const struct Location *loc,
                     bool include_end, bool include_slash,
                     char *buf, int len);

void set_location_end(struct Location *loc, const struct Location *from);

struct Location * shallow_copy_location(struct Location *loc);

#endif
