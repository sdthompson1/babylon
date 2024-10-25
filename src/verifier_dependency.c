/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "alloc.h"
#include "error.h"
#include "hash_table.h"
#include "scc.h"
#include "sexpr.h"
#include "stacked_hash_table.h"
#include "verifier_context.h"
#include "verifier_dependency.h"

#include <stdlib.h>
#include <string.h>

static void get_names_from_sexpr(const struct Sexpr *expr,
                                 struct HashTable *found_names,
                                 struct HashTable *shadowed_names,
                                 struct Edge **fake_edges);

static bool is_shadowed(struct HashTable *shadowed_names, const char *name)
{
    return hash_table_lookup(shadowed_names, name) != NULL;
}

static void add_shadowed_name(const struct Sexpr *name, struct HashTable *shadowed_names)
{
    if (name == NULL || name->type != S_STRING) {
        fatal_error("add_shadowed_name: wrong sexpr type");
    }

    uintptr_t n = (uintptr_t) hash_table_lookup(shadowed_names, name->string);
    hash_table_insert(shadowed_names, name->string, (void*)(n + 1));
}

static void remove_shadowed_name(const struct Sexpr *name, struct HashTable *shadowed_names)
{
    if (name == NULL || name->type != S_STRING) {
        fatal_error("remove_shadowed_name: wrong sexpr type");
    }

    uintptr_t n = (uintptr_t) hash_table_lookup(shadowed_names, name->string);
    if (n == 0) {
        fatal_error("not shadowed");
    }
    hash_table_insert(shadowed_names, name->string, (void*)(n - 1));
}

static void enter_scope_name_type_list(const struct Sexpr *list,
                                       struct HashTable *found_names,
                                       struct HashTable *shadowed_names,
                                       struct Edge **fake_edges)
{
    // List of (name type) pairs (or (name expr) pairs if this is a let).
    // The types/exprs should be scanned as normal, and the names should be added as shadowed.
    // The types/exprs must be done first, as these are not in the scope of the new bindings.
    for (const struct Sexpr *node = list; node; node = node->right) {
        // node->left is (name type)
        // node->left->right->left is type
        get_names_from_sexpr(node->left->right->left, found_names, shadowed_names, fake_edges);
    }
    for (const struct Sexpr *node = list; node; node = node->right) {
        // node->left is (name type)
        // node->left->left is name
        add_shadowed_name(node->left->left, shadowed_names);
    }
}

static void exit_scope_name_type_list(const struct Sexpr *list,
                                      struct HashTable *shadowed_names)
{
    while (list) {
        remove_shadowed_name(list->left->left, shadowed_names);
        list = list->right;
    }
}

static void enter_scope_pattern(const struct Sexpr *pat,
                                struct HashTable *found_names,
                                struct HashTable *shadowed_names,
                                struct Edge **fake_edges)
{
    // pat is either (ctorname list_of_bound_vars)
    // or a string ("$wildNN") - which is shadowed
    if (pat->type == S_STRING) {
        add_shadowed_name(pat, shadowed_names);
    } else if (pat->type == S_PAIR) {
        get_names_from_sexpr(pat->left, found_names, shadowed_names, fake_edges);  // ctorname
        for (struct Sexpr *node = pat->right; node; node = node->right) {
            add_shadowed_name(node->left, shadowed_names);
        }
    } else {
        fatal_error("unexpected sexpr type");
    }
}

static void exit_scope_pattern(const struct Sexpr *pat,
                               struct HashTable *shadowed_names)
{
    if (pat->type == S_STRING) {
        remove_shadowed_name(pat, shadowed_names);
    } else if (pat->type == S_PAIR) {
        for (struct Sexpr *node = pat->right; node; node = node->right) {
            remove_shadowed_name(node->left, shadowed_names);
        }
    } else {
        fatal_error("unexpected sexpr type");
    }
}

static void get_names_from_sexpr(const struct Sexpr *expr,
                                 struct HashTable *found_names,
                                 struct HashTable *shadowed_names,
                                 struct Edge **fake_edges)
{
    if (expr == NULL) {
        return;
    }

    switch (expr->type) {
    case S_STRING:
        ;
        const char *str = expr->string;
        if ((str[0] == '%' || str[0] == '$')
        && str[1] != 0
        && !is_shadowed(shadowed_names, str)) {

            if (!hash_table_contains_key(found_names, expr->string)) {

                hash_table_insert(found_names, expr->string, NULL);

                if (fake_edges) {
                    struct Edge *edge = alloc(sizeof(struct Edge));

                    // Here we are converting the char* expr->string pointer
                    // to struct Vertex *; it will be converted back to char*
                    // again later.
                    edge->target = (struct Vertex*) expr->string;

                    edge->next = *(fake_edges);
                    *fake_edges = edge;
                }
            }
        }
        break;

    case S_PAIR:
        if (expr->left && expr->left->type == S_STRING) {
            const char *str = expr->left->string;

            if (strcmp(str, "forall") == 0 || strcmp(str, "exists") == 0 || strcmp(str, "let") == 0) {
                // (forall/exists/let name_type_list expr)
                enter_scope_name_type_list(expr->right->left, found_names, shadowed_names, fake_edges);
                get_names_from_sexpr(expr->right->right->left, found_names, shadowed_names, fake_edges);
                exit_scope_name_type_list(expr->right->left, shadowed_names);
                break;

            } else if (strcmp(str, "define-fun") == 0) {
                // (define-fun name args rettype expr)
                enter_scope_name_type_list(expr->right->right->left, found_names, shadowed_names, fake_edges);
                get_names_from_sexpr(expr->right->right->right, found_names, shadowed_names, fake_edges); // covers rettype and expr
                exit_scope_name_type_list(expr->right->right->left, shadowed_names);
                break;

            } else if (strcmp(str, "match") == 0) {
                // (match expr arms)
                // each arm is: (pat rhs)
                get_names_from_sexpr(expr->right->left, found_names, shadowed_names, fake_edges);
                for (struct Sexpr *arm = expr->right->right->left; arm; arm = arm->right) {
                    enter_scope_pattern(arm->left->left, found_names, shadowed_names, fake_edges);
                    get_names_from_sexpr(arm->left->right->left, found_names, shadowed_names, fake_edges);
                    exit_scope_pattern(arm->left->left, shadowed_names);
                }
                break;
            }
        }

        get_names_from_sexpr(expr->left, found_names, shadowed_names, fake_edges);
        get_names_from_sexpr(expr->right, found_names, shadowed_names, fake_edges);
        break;

    default:
        fatal_error("unknown sexpr type");
    }
}

void get_free_var_names_in_sexpr(const struct Sexpr *expr,
                                 struct HashTable *var_names,
                                 struct HashTable *scratch)
{
    // this is a "public" version of get_names_from_sexpr
    hash_table_clear(scratch);
    get_names_from_sexpr(expr, var_names, scratch, NULL);
}

static struct Sexpr *strip_define_fun(struct Sexpr *expr)
{
    struct Sexpr *types = NULL;
    struct Sexpr **tail = &types;
    for (struct Sexpr *node = expr->right->right->left; node; node = node->right) {
        *tail = make_list1_sexpr(copy_sexpr(node->left->right->left));
        tail = &(*tail)->right;
    }
    return make_list4_sexpr(make_string_sexpr("declare-fun"),
                            copy_sexpr(expr->right->left),
                            types,
                            copy_sexpr(expr->right->right->right->left));
}

static struct Sexpr *try_strip_define_fun(struct Sexpr *expr,
                                          const struct HashTable *hidden_names)
{
    const char *name = expr->right->left->string;
    if (name[0] == '%' && hash_table_contains_key(hidden_names, &name[1])) {
        return strip_define_fun(expr);
    } else {
        return copy_sexpr(expr);
    }
}

static struct Sexpr *maybe_hide_defn(struct Sexpr *expr,
                                     const struct HashTable *hidden_names)
{
    // (define-fun name ((arg type) (arg type)) type value)
    // becomes
    // (declare-fun name (type type) type)
    if (hidden_names != NULL) {
        if (sexpr_equal_string(expr->left, "define-fun")) {
            return try_strip_define_fun(expr, hidden_names);
        } else if (sexpr_equal_string(expr->left, "generic")
                   && sexpr_equal_string(expr->right->right->right->left->left, "define-fun")) {
            return make_list4_sexpr(
                copy_sexpr(expr->left),
                copy_sexpr(expr->right->left),
                copy_sexpr(expr->right->right->left),
                try_strip_define_fun(expr->right->right->right->left, hidden_names));
        }
    }
    return copy_sexpr(expr);
}

struct Sexpr * get_sexpr_dependencies(const struct StackedHashTable *stack,
                                      bool use_all_layers,
                                      const struct HashTable *hidden_names,
                                      const struct Sexpr *expr,
                                      struct Sexpr *tail_sexpr) // handover
{
    struct HashTable *open_set = new_hash_table();
    struct HashTable *closed_set = new_hash_table();
    struct HashTable *shadowed_names = new_hash_table();  // this is just scratch space from our point of view

    struct Sexpr *result = NULL;
    struct Sexpr **tail_ptr = &result;

    // Initialise from expr
    get_names_from_sexpr(expr, open_set, shadowed_names, NULL);

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

                hash_table_insert(closed_set, name, NULL);

                struct Item *item = NULL;
                if (use_all_layers) {
                    item = stacked_hash_table_lookup(stack, name);
                } else {
                    item = hash_table_lookup(stack->table, name);
                }

                if (item) {
                    // Hide the definition if necessary.
                    struct Sexpr *new_decl = maybe_hide_defn(item->fol_decl, hidden_names);

                    // Add the decl to result list, and add any names it
                    // references to open set.
                    get_names_from_sexpr(new_decl, open_set, shadowed_names, NULL);
                    *tail_ptr = make_pair_sexpr(new_decl, NULL);
                    tail_ptr = &(*tail_ptr)->right;

                    // Same for axioms (but we don't hide the axioms, only
                    // the definition itself).
                    for (struct Sexpr *axiom = item->fol_axioms; axiom; axiom = axiom->right) {
                        get_names_from_sexpr(axiom->left, open_set, shadowed_names, NULL);
                        *tail_ptr = make_pair_sexpr(copy_sexpr(axiom->left), NULL);
                        tail_ptr = &(*tail_ptr)->right;
                    }
                }
            }
        }
    }

    free_hash_table(open_set);
    free_hash_table(closed_set);
    free_hash_table(shadowed_names);

    *tail_ptr = tail_sexpr;
    return result;
}


static void free_edge_list(struct Edge *edge)
{
    while (edge) {
        struct Edge *next = edge->next;
        free(edge);
        edge = next;
    }
}

static void free_graph(struct Vertex *vertex)
{
    while (vertex) {
        free_edge_list(vertex->edges);
        struct Vertex *next = vertex->next;
        free(vertex);
        vertex = next;
    }
}

static struct Component * reverse_component_list(struct Component *component)
{
    if (component == NULL) {
        return NULL;
    }

    struct Component *prev = NULL;
    while (component) {
        struct Component *next = component->next_component;
        component->next_component = prev;
        prev = component;
        component = next;
    }

    return prev;
}

static const char * get_defn_name(const struct Sexpr *defn)
{
    if (sexpr_equal_string(defn->left, "declare-const")
        || sexpr_equal_string(defn->left, "declare-fun")
        || sexpr_equal_string(defn->left, "define-fun")
        || sexpr_equal_string(defn->left, "declare-sort")
        || sexpr_equal_string(defn->left, "generic")) {
        return defn->right->left->string;
    } else if (sexpr_equal_string(defn->left, "declare-datatypes")) {
        return defn->right->left->left->left->string;
    } else {
        fatal_error("get_defn_name failed");
    }
}

struct Sexpr * reorder_sexpr_defns(struct Sexpr *defns,  // handover
                                   bool reverse_order)
{
    struct Vertex *vertices = NULL;

    struct HashTable *name_to_vertex = new_hash_table();
    struct HashTable *found_names = new_hash_table();
    struct HashTable *shadowed_names = new_hash_table();

    while (defns) {
        struct Sexpr *defn = defns->left;
        struct Sexpr *next = defns->right;
        free(defns);

        // make a vertex - taking ownership of defn
        struct Vertex *vertex = alloc(sizeof(struct Vertex));
        vertex->data = (void*) defn;
        vertex->edges = NULL;
        vertex->next = vertices;
        vertices = vertex;

        // insert it into the hash table
        const char *name = get_defn_name(defn);
        hash_table_insert(name_to_vertex, name, vertex);

        // for each name mentioned, add a "fake" Edge
        // (it is "fake" because the target points to a string rather than
        // a Vertex but we will fix that up later)
        hash_table_clear(found_names);
        get_names_from_sexpr(defn, found_names, shadowed_names, &vertex->edges);

        defns = next;
    }

    free_hash_table(found_names);
    free_hash_table(shadowed_names);

    // Fix the fake edges to point to actual vertices
    for (struct Vertex *v = vertices; v; v = v->next) {
        for (struct Edge *e = v->edges; e; e = e->next) {
            void *value = hash_table_lookup(name_to_vertex, (const char *)e->target);
            e->target = (struct Vertex *) value;
        }
    }

    free_hash_table(name_to_vertex);

    // Do connected components.
    struct Component *component = strongly_connected_components(vertices);
    free_graph(vertices);

    if (reverse_order) {
        component = reverse_component_list(component);
    }

    // Build the output list - transferring ownership of the sexprs to
    // the output.
    struct Sexpr *output = NULL;
    struct Sexpr **output_tail = &output;

    while (component) {
        struct ComponentVertex *vertex = component->first_vertex;
        while (vertex) {
            *output_tail = make_list1_sexpr(vertex->vertex_data);
            output_tail = &(*output_tail)->right;

            struct ComponentVertex *to_free = vertex;
            vertex = vertex->next;
            free(to_free);
        }

        struct Component *to_free = component;
        component = component->next_component;
        free(to_free);
    }

    return output;
}
