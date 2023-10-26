/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "convert_fol_to_smt.h"
#include "error.h"
#include "hash_table.h"
#include "sexpr.h"
#include "stringbuf.h"
#include "util.h"

#include <ctype.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// assumption: name does not contain '!' nor '-'
static char* make_encoded_name(struct HashTable *encodings,
                               struct StringBuf *buf,
                               const char *name,
                               struct Sexpr *args)
{
    if (args == NULL) {
        return copy_string(name);

    } else {
        // make a key out of "!" + name + formatted arguments.
        stringbuf_clear(buf);
        stringbuf_append(buf, "!");
        stringbuf_append(buf, name);
        format_sexpr(buf, args);

        // have we encountered this key before?
        void *value = hash_table_lookup(encodings, buf->data);
        if (value) {
            // yes, return the existing name
            return copy_string(value);

        } else {
            // no
            // have we at least encountered this name before?
            uint32_t *v = hash_table_lookup(encodings, name);

            if (v == NULL) {
                // no. make a new counter for this name starting at zero
                v = malloc(sizeof(uint32_t));
                *v = 0;
                hash_table_insert(encodings, copy_string(name), v);

            } else if (*v == UINT32_MAX) {
                fatal_error("make_encoded_name: overflow");

            } else {
                // yes, encountered this name before.
                // use the previous counter value plus one.
                *v += 1;
            }

            // we will use the name plus "-" plus the counter value.
            char suffix[30];
            sprintf(suffix, "-%" PRIu32, *v);
            char *new_name = copy_string_2(name, suffix);

            // save the new_name so that next time we see this name+arguments combo,
            // we will encode it to the same thing.
            hash_table_insert(encodings, copy_string(buf->data), copy_string(new_name));
            return new_name;
        }
    }
}

static struct Sexpr * make_prod_definition(struct HashTable *encodings,
                                           struct StringBuf *buf,
                                           const char *encoded_name,
                                           struct Sexpr *types)
{
    struct Sexpr *fields = NULL;
    struct Sexpr **tail = &fields;

    int num = 0;
    char scratch[30];

    for (struct Sexpr *type_node = types; type_node; type_node = type_node->right) {
        sprintf(scratch, "$FLD%d", num++);

        struct Sexpr *field =
            make_list2_sexpr(
                make_string_sexpr_handover(make_encoded_name(encodings, buf, scratch, types)),
                copy_sexpr(type_node->left));

        *tail = make_list1_sexpr(field);
        tail = &(*tail)->right;
    }

    return make_list3_sexpr(
        make_string_sexpr("declare-datatypes"),
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr(encoded_name),
                make_string_sexpr("0"))),
        make_list1_sexpr(      // 1 type being defined
            make_list1_sexpr(  // 1 constructor
                make_pair_sexpr(
                    make_string_sexpr(encoded_name),
                    fields))));
}

static struct Sexpr * make_sum_definition(struct HashTable *encodings,
                                          struct StringBuf *buf,
                                          const char *encoded_name,
                                          struct Sexpr *types)
{
    struct Sexpr *variants = NULL;
    struct Sexpr **tail = &variants;

    int num = 0;
    char scratch[30];

    for (struct Sexpr *type_node = types; type_node; type_node = type_node->right) {
        sprintf(scratch, "$IN%d", num);
        char *in_name = make_encoded_name(encodings, buf, scratch, types);

        sprintf(scratch, "$INF%d", num);
        char *inf_name = make_encoded_name(encodings, buf, scratch, types);

        ++num;

        struct Sexpr *variant =
            make_list2_sexpr(
                make_string_sexpr_handover(in_name),
                make_list2_sexpr(
                    make_string_sexpr_handover(inf_name),
                    copy_sexpr(type_node->left)));

        *tail = make_list1_sexpr(variant);
        tail = &(*tail)->right;
    }

    return make_list3_sexpr(
        make_string_sexpr("declare-datatypes"),
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr(encoded_name),
                make_string_sexpr("0"))),
        make_list1_sexpr(variants));
}

static struct Sexpr * instantiate(struct HashTable *encodings,
                                  struct StringBuf *buf,
                                  struct Sexpr *generics,
                                  const char *name,
                                  const char *encoded_name,
                                  struct Sexpr *arglist)
{
    // special cases
    if (strcmp(name, "$PROD") == 0) {
        return make_list1_sexpr(make_prod_definition(encodings, buf, encoded_name, arglist));
    } else if (strcmp(name, "$SUM") == 0) {
        return make_list1_sexpr(make_sum_definition(encodings, buf, encoded_name, arglist));
    }

    // it must be a user-defined name, look for any "generic" commands to instantiate

    struct Sexpr *list = NULL;
    struct Sexpr **tail_ptr = &list;

    for (struct Sexpr *command_node = generics; command_node; command_node = command_node->right) {

        struct Sexpr *command = command_node->left;

        // command is of the form:
        // (generic name (variables) decl)
        if (sexpr_equal_string(command->right->left, name)) {

            struct Sexpr *keys =
                make_pair_sexpr(make_string_sexpr(name),
                                copy_sexpr(command->right->right->left));

            struct Sexpr *values =
                make_pair_sexpr(make_string_sexpr(encoded_name),
                                copy_sexpr(arglist));

            struct Sexpr *new_decl =
                substitute_in_sexpr(keys, values, command->right->right->right->left);

            free_sexpr(keys);
            free_sexpr(values);

            *tail_ptr = make_list1_sexpr(new_decl);
            tail_ptr = &((*tail_ptr)->right);
        }
    }

    return list;
}

// Replace "instance" keywords with encoded names, appending any required
// new definitions to the "tail_ptr".
// Replace "(prove ...)" with "(assert (not ...))".
// Return the new sexpr.
static struct Sexpr * scan_sexpr(struct HashTable *encodings,
                                 struct HashTable *closed_set,
                                 struct StringBuf *buf,
                                 struct Sexpr *generics,
                                 struct Sexpr ***tail_ptr,
                                 struct Sexpr *sexpr)
{
    // (instance name (args))
    if (sexpr && sexpr->type == S_PAIR && sexpr_equal_string(sexpr->left, "instance")) {

        // copy out the bits we need (and encode the name)
        const char *name = copy_string(sexpr->right->left->string);
        struct Sexpr *args = copy_sexpr(sexpr->right->right->left);
        const char *encoded_name = make_encoded_name(encodings, buf, name, args);

        // make the result
        struct Sexpr *result = make_string_sexpr(encoded_name);

        // now we need to instantiate the definition.
        // usually we want a definition of "name", but a special case is name == "$INnnn"
        // (where nnn are digits), in which case we need the definition of "$SUM" instead
        if (name[0] == '$' && name[1] == 'I' && name[2] == 'N' && isdigit((unsigned char)name[3])) {
            free((char*)name);
            name = copy_string("$SUM");
            free((char*)encoded_name);
            encoded_name = make_encoded_name(encodings, buf, name, args);
        }

        // have the definitions for this instance already been created?
        if (!hash_table_contains_key(closed_set, encoded_name)) {

            // make the definitions for this instance
            struct Sexpr *instances =
                instantiate(encodings, buf, generics, name, encoded_name, args);

            hash_table_insert(closed_set, encoded_name, NULL);

            // recursively scan the definitions to see if they themselves
            // have instances that need to be resolved
            struct Sexpr *new_instances = scan_sexpr(encodings, closed_set, buf,
                                                     generics, tail_ptr, instances);
            free_sexpr(instances);

            // now add the new definitions into the list
            **tail_ptr = new_instances;
            while (**tail_ptr) {
                *tail_ptr = &((**tail_ptr)->right);
            }

        } else {
            free((char*)encoded_name);
            encoded_name = NULL;
        }

        free((char*)name);
        name = NULL;

        free_sexpr(args);
        free((char*)name);

        return result;

    } else if (sexpr && sexpr->type == S_PAIR && sexpr_equal_string(sexpr->left, "prove")) {
        // (prove EXPR) --> (assert (not NEW_EXPR))
        struct Sexpr *new_expr = scan_sexpr(encodings, closed_set, buf,
                                            generics, tail_ptr, sexpr->right->left);
        return make_list2_sexpr(make_string_sexpr("assert"),
                                make_list2_sexpr(make_string_sexpr("not"),
                                                 new_expr));

    } else if (sexpr && sexpr->type == S_PAIR) {
        // not an "instance". just recursively process the left and right,
        // then combine them together into a new node
        struct Sexpr *new_left = scan_sexpr(encodings, closed_set, buf, generics, tail_ptr, sexpr->left);
        struct Sexpr *new_right = scan_sexpr(encodings, closed_set, buf, generics, tail_ptr, sexpr->right);
        return make_pair_sexpr(new_left, new_right);

    } else {
        // just copy it
        return copy_sexpr(sexpr);
    }
}

struct Sexpr * convert_fol_to_smt(struct Sexpr * fol_problem)
{
    // Let's first take all the generics out of the fol_problem
    struct Sexpr *generics = NULL;
    struct Sexpr **generic_tail_ptr = &generics;

    struct Sexpr **link = &fol_problem;
    for (struct Sexpr *node = fol_problem; node; ) {

        struct Sexpr *command = node->left;

        if (command->type == S_PAIR
        && sexpr_equal_string(command->left, "generic")) {

            *generic_tail_ptr = make_list1_sexpr(command);
            generic_tail_ptr = &((*generic_tail_ptr)->right);

            *link = node->right;

            free(node);
            node = *link;

        } else {
            link = &node->right;
            node = node->right;
        }
    }


    // Now copy the remaining fol_problem to the output, instantiating
    // generics as we go along.
    struct StringBuf buf;
    stringbuf_init(&buf);

    struct Sexpr *result = NULL;
    struct Sexpr **result_tail_ptr = &result;

    struct HashTable *encodings = new_hash_table();
    struct HashTable *closed_set = new_hash_table();

    for (struct Sexpr *node = fol_problem; node; node = node->right) {
        struct Sexpr *command = node->left;

        struct Sexpr *new_command = scan_sexpr(encodings, closed_set, &buf, generics,
                                               &result_tail_ptr, command);

        *result_tail_ptr = make_list1_sexpr(new_command);
        result_tail_ptr = &((*result_tail_ptr)->right);
    }


    // Append (check-sat)
    *result_tail_ptr = make_list1_sexpr(make_list1_sexpr(make_string_sexpr("check-sat")));


    // Clean up
    free_sexpr(generics);
    free_sexpr(fol_problem);

    stringbuf_free(&buf);

    hash_table_for_each(closed_set, ht_free_key, NULL);
    free_hash_table(closed_set);

    hash_table_for_each(encodings, ht_free_key_and_value, NULL);
    free_hash_table(encodings);

    return result;
}
