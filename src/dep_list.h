/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef DEP_LIST_H
#define DEP_LIST_H

struct DepList {
    char *name;                   // allocated
    char *min_version;            // allocated
    struct DepList *next;
};

#endif
