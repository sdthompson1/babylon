/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"
#include "hash_table.h"
#include "scc.h"
#include "sexpr.h"
#include "verifier_context.h"
#include "verifier_dependency.h"

#include <stdlib.h>

struct GetNamesContext {
    struct HashTable *found_names;
    struct Edge **fake_edges;
};

static void* get_names_from_string_sexpr(void *cxt, struct Sexpr *expr)
{
    struct GetNamesContext *context = (struct GetNamesContext*) cxt;

    if ((expr->string[0] == '%' || expr->string[0] == '$')
    && expr->string[1] != 0) {
        hash_table_insert(context->found_names, expr->string, NULL);

        if (context->fake_edges) {
            struct Edge *edge = alloc(sizeof(struct Edge));

            // Here I'm assuming that it's safe to convert a char*
            // (allocated) pointer to a struct Vertex* pointer, and
            // back again (later on). This should be fine (C11,
            // section 6.3.2.3 paragraph 7 -- we may assume that a
            // malloc-returned pointer is aligned for any struct
            // type).
            edge->target = (struct Vertex*) expr->string;

            edge->next = *(context->fake_edges);
            *(context->fake_edges) = edge;
        }
    }

    return NULL;
}

static void get_names_from_sexpr(const struct Sexpr *expr,
                                 struct HashTable *found_names,
                                 struct Edge **fake_edges)
{
    struct GetNamesContext context;
    context.found_names = found_names;
    context.fake_edges = fake_edges;

    struct SexprTransform tr = {0};
    tr.transform_string = get_names_from_string_sexpr;

    transform_sexpr(&tr, &context, (struct Sexpr*)expr);
}


// Returns a graph in which the Vertex "data" is a name (char*) used
// in the problem, and the edges point to dependencies (i.e. decls
// that have to appear before this one in the FOL problem).
static struct Vertex * build_decl_graph(const struct HashTable *env1,
                                        const struct HashTable *env2,
                                        const struct Sexpr *expr1,
                                        const struct Sexpr *expr2)
{
    struct HashTable *open_set = new_hash_table();
    struct HashTable *closed_set = new_hash_table();
    struct Vertex *vertices = NULL;

    // Initialise from expr1 and expr2
    get_names_from_sexpr(expr1, open_set, NULL);
    get_names_from_sexpr(expr2, open_set, NULL);

    // Iterate until the open set is empty
    while (!hash_table_empty(open_set)) {

        // Pop an item from the open set
        const char *name;
        void *value;
        hash_table_get_first(open_set, &name, &value);
        if (name) {
            hash_table_remove_first(open_set);

            // We are going to add this to the closed set, if it is
            // not there already
            if (!hash_table_contains_key(closed_set, name)) {

                struct Item *item = NULL;
                if (env1) {
                    item = hash_table_lookup(env1, name);
                }
                if (!item && env2) {
                    item = hash_table_lookup(env2, name);
                }

                if (item) {
                    // Build vertex.
                    struct Vertex *vertex = alloc(sizeof(struct Vertex));
                    vertex->data = (void*) name;
                    vertex->edges = NULL;
                    vertex->next = vertices;
                    vertices = vertex;

                    // Add all names referenced by this name to the open set.

                    // Also add Edges -- but we cannot add Vertex
                    // pointers yet, because we haven't created all
                    // the vertices yet. Instead add the names (cast
                    // to Vertex *) and we will fix it up later.

                    get_names_from_sexpr(item->fol_decl, open_set, &vertex->edges);
                    for (struct Sexpr *axiom = item->fol_axioms; axiom; axiom = axiom->right) {
                        get_names_from_sexpr(axiom->left, open_set, &vertex->edges);
                    }

                    // Add the vertex itself to the closed set.
                    hash_table_insert(closed_set, name, vertex);
                }
            }
        }
    }

    free_hash_table(open_set);

    // Now "fix" all the edge target pointers
    for (struct Vertex *v = vertices; v; v = v->next) {
        for (struct Edge *e = v->edges; e; e = e->next) {
            void *value = hash_table_lookup(closed_set, (const char*)e->target);
            e->target = (struct Vertex*) value;
        }
    }

    free_hash_table(closed_set);

    // Done!
    return vertices;
}

static void free_graph(struct Vertex *vertex)
{
    while (vertex) {
        struct Edge *edge = vertex->edges;
        while (edge) {
            struct Edge *next = edge->next;
            free(edge);
            edge = next;
        }
        struct Vertex *next = vertex->next;
        free(vertex);
        vertex = next;
    }
}

struct Component * get_sexpr_dependencies(const struct HashTable *env1,
                                          const struct HashTable *env2,
                                          const struct Sexpr *expr1,
                                          const struct Sexpr *expr2)
{
    struct Vertex *graph = build_decl_graph(env1, env2, expr1, expr2);
    struct Component *components = strongly_connected_components(graph);
    free_graph(graph);
    return components;
}
