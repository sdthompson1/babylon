/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef SCC_H
#define SCC_H

#include <stdbool.h>

struct Edge;

struct Vertex {
    void *data;
    struct Edge *edges;
    struct Vertex *next;

    // for internal use by the algorithm (does not need to be initialised)
    int index;
    int lowlink;
    bool on_stack;
};

struct Edge {
    struct Vertex *target;
    struct Edge *next;
};

struct ComponentVertex {
    void *vertex_data;
    struct ComponentVertex *next;
};

struct Component {
    struct ComponentVertex *first_vertex;
    struct Component *next_component;
};

// The returned Component and ComponentVertex structures are allocated on the heap
struct Component * strongly_connected_components(struct Vertex *vertices);

#endif
