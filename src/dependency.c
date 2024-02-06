/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "dependency.h"
#include "hash_table.h"
#include "names.h"
#include "scc.h"
#include "util.h"

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

static void fill_dependency_names(struct HashTable *names, struct Decl *decl)
{
    struct NameList *list = NULL;
    struct HashIterator *iter = new_hash_iterator(names);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        // For this, we only care about dependencies on global names,
        // i.e. names that contain a dot.
        if (strchr(key, '.') != NULL) {
            struct NameList *node = alloc(sizeof(struct NameList));
            node->name = copy_string(key);
            node->next = list;
            list = node;
        }
    }
    free_hash_iterator(iter);

    decl->dependency_names = sort_name_list(list);
}

static void resolve_group(struct DeclGroup **group)
{
    if (*group == NULL) {
        return;
    }

    // Create vertices
    // Also create a hash table mapping symbol name to vertex pointer

    struct Vertex *vertices = NULL;
    struct Vertex **tail_ptr = &vertices;

    struct HashTable *name_to_vertex = new_hash_table();

    struct Decl *decl = (*group)->decl;

    while (decl) {
        struct Vertex *new_vertex = alloc(sizeof(struct Vertex));
        new_vertex->data = decl;
        new_vertex->edges = NULL;
        new_vertex->next = NULL;

        *tail_ptr = new_vertex;
        tail_ptr = &new_vertex->next;

        hash_table_insert(name_to_vertex, decl->name, new_vertex);

        decl = decl->next;
    }

    // Create edges
    struct Vertex *v = vertices;
    while (v) {
        struct HashTable *names_in_v = new_hash_table();
        names_used_in_decl(names_in_v, (struct Decl*) v->data);

        fill_dependency_names(names_in_v, (struct Decl*) v->data);

        struct HashIterator *iterator = new_hash_iterator(names_in_v);
        const char *key;
        void *value;
        while (hash_iterator_next(iterator, &key, &value)) {
            struct Vertex *to_vertex = hash_table_lookup(name_to_vertex, key);
            if (to_vertex != NULL) {
                struct Edge *edge = alloc(sizeof(struct Edge));
                edge->target = to_vertex;
                edge->next = v->edges;
                v->edges = edge;
            }
            if (to_vertex == v) {
                ((struct Decl*)(v->data))->recursive = true;  // self-recursion
            }
        }

        free_hash_iterator(iterator);
        free_hash_table(names_in_v);

        v = v->next;
    }

    // Call connected components algorithm
    struct Component *component = strongly_connected_components(vertices);

    // Free the hash table (and all vertices and edges within)
    struct HashIterator * iter = new_hash_iterator(name_to_vertex);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct Vertex *vertex = value;
        struct Edge *edge = vertex->edges;
        while (edge) {
            struct Edge *next = edge->next;
            free(edge);
            edge = next;
        }
        free(vertex);
    }
    free_hash_iterator(iter);
    free_hash_table(name_to_vertex);

    // Write the results back
    free(*group);  // not free_decl_group as we want to keep all the Decls
    *group = NULL;
    struct DeclGroup **group_tail_ptr = group;

    // Iterate through Components and ComponentVertexes (freeing them as we go)
    while (component) {
        struct DeclGroup *new_group = alloc(sizeof(struct DeclGroup));
        new_group->decl = NULL;
        new_group->next = NULL;

        struct Decl **decl_tail_ptr = &new_group->decl;

        *group_tail_ptr = new_group;
        group_tail_ptr = &(new_group->next);

        struct ComponentVertex *cv = component->first_vertex;
        while (cv) {
            struct Decl *decl = (struct Decl*)(cv->vertex_data);
            *decl_tail_ptr = decl;
            decl->next = NULL;
            decl_tail_ptr = &(decl->next);

            struct ComponentVertex *to_free = cv;
            cv = cv->next;
            free(to_free);
        }

        if (new_group->decl->next) {
            for (struct Decl *decl = new_group->decl; decl; decl = decl->next) {
                decl->recursive = true;
            }
        }

        struct Component *to_free = component;
        component = component->next_component;
        free(to_free);
    }
}

void resolve_dependencies(struct Module *module)
{
    resolve_group(&module->interface);
    resolve_group(&module->implementation);
}
