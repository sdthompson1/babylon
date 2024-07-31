/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "dependency.h"
#include "error.h"
#include "hash_table.h"
#include "names.h"
#include "scc.h"
#include "util.h"

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

struct Graph {
    struct Vertex *vertices_head;  // points to first vertex or NULL
    struct Vertex *vertices_tail;  // points to last vertex or NULL
    struct HashTable *name_to_vertex;
    struct HashTable *name_to_interface_decl;
    struct HashTable *name_to_impl_decl;
};

static void init_graph(struct Graph *graph)
{
    graph->vertices_head = NULL;
    graph->vertices_tail = NULL;
    graph->name_to_vertex = new_hash_table();
    graph->name_to_interface_decl = new_hash_table();
    graph->name_to_impl_decl = new_hash_table();
}

static void free_graph(struct Graph *graph)
{
    struct Vertex *vertex = graph->vertices_head;
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

    free_hash_table(graph->name_to_vertex);
    free_hash_table(graph->name_to_interface_decl);
    free_hash_table(graph->name_to_impl_decl);
}

// Add a new vertex (corresponding to a Decl) to the graph.
// vertex->data is the decl name.
// (If the vertex already exists, it is not added again, but it may be moved in the list.)
static void add_vertex(struct Graph *graph, struct Decl *decl, bool impl)
{
    struct Vertex *vertex = hash_table_lookup(graph->name_to_vertex, decl->name);

    if (vertex) {
        // Already existing vertex. Move it to the end of the list
        // (this doesn't affect the dependency algorithm itself, but
        // it makes the compiler error messages appear in a nicer order!).
        if (vertex != graph->vertices_tail) {

            // remove from list
            if (vertex->next) {
                vertex->next->prev = vertex->prev;
            }
            if (vertex->prev) {
                vertex->prev->next = vertex->next;
            }
            if (vertex == graph->vertices_head) {
                graph->vertices_head = vertex->next;
            }

            // append to list
            graph->vertices_tail->next = vertex;
            vertex->next = NULL;
            vertex->prev = graph->vertices_tail;
            graph->vertices_tail = vertex;
        }

    } else {
        // This is a new vertex. Add it to the end of the list.
        vertex = alloc(sizeof(struct Vertex));
        vertex->data = (void*)decl->name;
        vertex->edges = NULL;
        vertex->prev = graph->vertices_tail;
        vertex->next = NULL;

        if (graph->vertices_tail) {
            graph->vertices_tail->next = vertex;
            graph->vertices_tail = vertex;
        } else {
            graph->vertices_head = graph->vertices_tail = vertex;
        }

        hash_table_insert(graph->name_to_vertex, decl->name, vertex);
    }

    // Also add the data ctor names (as "alternative names" for
    // this vertex), if applicable.
    if (decl->tag == DECL_DATATYPE) {
        for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
            hash_table_insert(graph->name_to_vertex, ctor->name, vertex);
        }
    }

    if (impl) {
        hash_table_insert(graph->name_to_impl_decl, decl->name, decl);
    } else {
        hash_table_insert(graph->name_to_interface_decl, decl->name, decl);
    }
}

// Add edges to the graph, corresponding to the dependencies of the given Decl.
// (Assumes all Vertices have been created already.)
// Also set "dependency_names" on the decl.
static void add_edges(struct Graph *graph, struct Decl *decl)
{
    struct Vertex *vertex = hash_table_lookup(graph->name_to_vertex, decl->name);
    if (!vertex) {
        fatal_error("vertex not found");
    }

    struct HashTable *names = new_hash_table();
    names_used_in_decl(names, decl);

    struct HashIterator *iterator = new_hash_iterator(names);
    const char *key;
    void *value;
    while (hash_iterator_next(iterator, &key, &value)) {
        struct Vertex *to_vertex = hash_table_lookup(graph->name_to_vertex, key);

        if (to_vertex == vertex) {
            // Self-recursion.
            // (Note: this "if" also triggers in things like datatype Color = Red, because
            // "Red" is an alternative name for the "Color" vertex -- but this should not
            // be considered self-recursion. A strcmp will catch this case.)
            if (strcmp(key, to_vertex->data) == 0) {
                decl->recursive = true;
            }

        } else {
            if (to_vertex != NULL) {
                // add new edge to the front of the list
                struct Edge *edge = alloc(sizeof(struct Edge));
                edge->target = to_vertex;
                edge->next = vertex->edges;
                vertex->edges = edge;
            }

            // If it is a global name (containing a '.'), add to dependency_names.
            // Note that this should happen regardless of whether to_vertex is NULL or not,
            // because we want to catch both intra- and inter-module dependencies.
            if (strchr(key, '.') != NULL) {
                struct NameList *node = alloc(sizeof(struct NameList));
                node->name = copy_string(key);
                node->next = decl->dependency_names;
                decl->dependency_names = node;
            }
        }
    }

    free_hash_iterator(iterator);
    free_hash_table(names);

    decl->dependency_names = sort_name_list(decl->dependency_names);
}


static void resolve_group(struct Graph *graph, struct DeclGroup **group, bool impl)
{
    if (*group == NULL) {
        return;
    }

    // Add all decls as Vertices
    for (struct Decl *decl = (*group)->decl; decl; decl = decl->next) {
        add_vertex(graph, decl, impl);
    }

    // Add the edges
    for (struct Decl *decl = (*group)->decl; decl; decl = decl->next) {
        add_edges(graph, decl);
    }

    // Compute connected components
    struct Component *component = strongly_connected_components(graph->vertices_head);

    // Write the results back
    free(*group);  // not free_decl_group as we want to keep all the Decls
    *group = NULL;
    struct DeclGroup **group_tail_ptr = group;

    // Iterate through Components and ComponentVertexes (freeing them as we go)
    while (component) {
        struct Decl *decl_list = NULL;
        struct Decl **decl_tail_ptr = &decl_list;

        struct ComponentVertex *cv = component->first_vertex;
        while (cv) {
            const char *name = (const char*)(cv->vertex_data);

            struct Decl *decl = NULL;
            if (impl) {
                decl = hash_table_lookup(graph->name_to_impl_decl, name);
            } else {
                decl = hash_table_lookup(graph->name_to_interface_decl, name);
            }

            if (decl) {
                *decl_tail_ptr = decl;
                decl->next = NULL;
                decl_tail_ptr = &(decl->next);
            }

            struct ComponentVertex *to_free = cv;
            cv = cv->next;
            free(to_free);
        }

        if (decl_list) {
            struct DeclGroup *new_group = alloc(sizeof(struct DeclGroup));
            new_group->decl = decl_list;
            new_group->next = NULL;
            *group_tail_ptr = new_group;
            group_tail_ptr = &(new_group->next);

            if (decl_list->next) {
                for (struct Decl *decl = decl_list; decl; decl = decl->next) {
                    decl->recursive = true;
                }
            }
        }

        struct Component *to_free = component;
        component = component->next_component;
        free(to_free);
    }
}

void resolve_dependencies(struct Module *module)
{
    struct Graph graph;
    init_graph(&graph);
    resolve_group(&graph, &module->interface, false);
    resolve_group(&graph, &module->implementation, true);
    free_graph(&graph);
}
