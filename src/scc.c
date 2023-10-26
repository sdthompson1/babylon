/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "scc.h"

#include <stdlib.h>

struct StackEntry {
    struct Vertex *vertex;
    struct StackEntry *next;
};

static void strongconnect(struct Component **output_head,
                          struct Component **output_tail,
                          struct Vertex *v,
                          struct StackEntry **stack,
                          int *index)
{
    // Set the depth index for v to the smallest unused index
    v->index = *index;
    v->lowlink = *index;
    (*index)++;

    // Push v onto the stack
    struct StackEntry *new_stack = alloc(sizeof(struct StackEntry));
    new_stack->vertex = v;
    new_stack->next = *stack;
    *stack = new_stack;
    v->on_stack = true;

    // Consider successors of v
    struct Edge *edge = v->edges;
    while (edge) {
        if (edge->target != NULL) {
            if (edge->target->index == -1) {
                // Successor has not yet been visited; recurse on it
                strongconnect(output_head, output_tail, edge->target, stack, index);
                if (edge->target->lowlink < v->lowlink) {
                    v->lowlink = edge->target->lowlink;
                }
            } else if (edge->target->on_stack) {
                // Successor is in stack and hence in the current SCC
                if (edge->target->index < v->lowlink) {
                    v->lowlink = edge->target->index;
                }
            }
        }
        edge = edge->next;
    }

    // If v is a root node, pop the stack and generate an SCC
    // (add it to the END of the list)
    if (v->lowlink == v->index) {
        struct Component *new_component = alloc(sizeof(struct Component));
        new_component->first_vertex = NULL;
        new_component->next_component = NULL;

        if (*output_head == NULL) {
            *output_head = new_component;
        } else {
            (*output_tail)->next_component = new_component;
        }
        *output_tail = new_component;

        struct Vertex *w = NULL;
        while (w != v) {
            // pop vertex 'w' from top of stack
            w = (*stack)->vertex;
            struct StackEntry *to_free = *stack;
            *stack = (*stack)->next;
            free(to_free);
            w->on_stack = false;

            // add w to current SCC
            // (order of vertices within SCC doesn't matter, so just add to front)
            struct ComponentVertex *cv = alloc(sizeof(struct ComponentVertex));
            cv->vertex_data = w->data;
            cv->next = new_component->first_vertex;
            new_component->first_vertex = cv;
        }
    }
}

struct Component * strongly_connected_components(struct Vertex *vertices)
{
    struct Component *result_head = NULL;
    struct Component *result_tail = NULL;

    int index = 0;
    struct StackEntry *stack = NULL;

    for (struct Vertex *v = vertices; v; v = v->next) {
        v->index = -1;
        v->lowlink = -1;
        v->on_stack = false;
    }

    for (struct Vertex *v = vertices; v; v = v->next) {
        if (v->index == -1) {
            strongconnect(&result_head, &result_tail, v, &stack, &index);
        }
    }

    return result_head;
}
