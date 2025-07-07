/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "hash_table.h"
#include "package.h"
#include "renamer.h"
#include "util.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct LocalName {
    // If the variable is currently in scope, this gives the scope number at which it
    // was declared. (Outermost scope is number 1, next scope down is number 2, etc.)
    // If the variable has gone out of scope, this will be zero.
    int scope_number;

    // If the variable is currently in scope, this is the current "@" number
    // we are using for it. (If zero, there will be no "@" suffix.)
    uint64_t version_number;

    // Highest "@" number we have ever used for this variable.
    uint64_t highest_version_number;
};

struct RenamerState {
    // Renamer env.
    // Key = pkg-name/ModuleName (allocated)
    // Value = NameList of (unqualified) names exported by this module.
    // (Note: we use '/' in the key to separate the pkg-name from
    // the ModName; ':' might have been better, but ':' is not a legal
    // character for SMT-LIB variable names, unfortunately.)
    struct HashTable *renamer_env;

    // Information about the current module
    struct Module *module;
    const char *module_name_without_package;  // current module name, without its package-name
    bool error;

    // Current scope number
    int current_scope;

    // Flags used to determine if "return" can legally be used as a variable name
    bool in_postcondition;
    bool function_returns_value;


    // Local names
    // Key = name (allocated), value = LocalName pointer (allocated).
    struct HashTable *local_names;

    // Global names from this module
    // Key = name (unqualified) (allocated)
    // Value = NULL
    struct HashTable *interface_names;
    struct HashTable *implementation_names;

    // Global names from other modules
    // Key = name ("xyz" or "ModAlias.xyz") (allocated)
    // Value = NameList of qualified names ("pkg-name/ModName.name") that it can
    //   resolve to (allocated)
    struct HashTable *imported_names;


    // The set of module aliases in use
    // Key = module alias (shared with AST)
    // Value = NULL
    // Does not include the current module name itself.
    struct HashTable *module_aliases;


    // If this is non-NULL, special mode for match compiler is active
    uint64_t * match_compiler_counter;
};

static void free_name_and_namelist(void *context, const char *key, void *value)
{
    free((char*)key);
    free_name_list(value);
}

void free_renamer_env(struct HashTable *env)
{
    hash_table_for_each(env, free_name_and_namelist, NULL);
    free_hash_table(env);
}

static void init_renamer_state(struct RenamerState *state)
{
    state->renamer_env = NULL;
    state->module = NULL;
    state->error = false;
    state->current_scope = 0;
    state->in_postcondition = false;
    state->function_returns_value = false;
    state->local_names = new_hash_table();
    state->interface_names = new_hash_table();
    state->implementation_names = new_hash_table();
    state->imported_names = new_hash_table();
    state->module_aliases = new_hash_table();
    state->match_compiler_counter = NULL;
    state->module_name_without_package = NULL;
}

static void reset_local_names(struct RenamerState *state)
{
    state->current_scope = 1;
    hash_table_for_each(state->local_names, ht_free_key_and_value, NULL);
    hash_table_clear(state->local_names);
}

static void clean_up_renamer_state(struct RenamerState *state)
{
    reset_local_names(state);
    free_hash_table(state->local_names);

    hash_table_for_each(state->interface_names, ht_free_key, NULL);
    free_hash_table(state->interface_names);

    hash_table_for_each(state->implementation_names, ht_free_key, NULL);
    free_hash_table(state->implementation_names);

    hash_table_for_each(state->imported_names, free_name_and_namelist, NULL);
    free_hash_table(state->imported_names);

    free_hash_table(state->module_aliases);

    free((char*)state->module_name_without_package);
}


static void add_hat(const char ** name)
{
    if (**name != '^') {
        char * new_name = copy_string_2("^", *name);
        free((char*)*name);
        *name = new_name;
    }
}


// Rename a newly declared local (e.g. the name in a vardecl stmt,
// or a type variable name).
// (Can issue "duplicate variable" error if the variable has already
// been declared in the same scope.)
// Optionally also returns old scope and version numbers in case the
// variable needs to be "reset" afterwards.
// Does not add "^" for types; this must be done separately.
static void add_new_local_name(struct RenamerState *state,
                               struct Location location,
                               const char **name,
                               struct LocalName **ptr,
                               int *old_scope,
                               uint64_t *old_version)
{
    struct LocalName *local = hash_table_lookup(state->local_names, *name);

    if (local == NULL) {
        local = alloc(sizeof(struct LocalName));
        local->scope_number = state->current_scope;
        local->version_number = 0;
        local->highest_version_number = 0;
        hash_table_insert(state->local_names, copy_string(*name), local);

        if (old_scope) *old_scope = 0;
        if (old_version) *old_version = 0;

    } else {
        if (old_scope) *old_scope = local->scope_number;
        if (old_version) *old_version = local->version_number;

        if (local->scope_number < state->current_scope) {
            local->scope_number = state->current_scope;

            if (state->match_compiler_counter) {
                local->version_number = (*state->match_compiler_counter)++;
            } else {
                local->version_number = local->highest_version_number + 1u;
                local->highest_version_number ++;
            }

            char buf[40];
            sprintf(buf,
                    "@%s%" PRIu64,
                    state->match_compiler_counter ? "copy" : "",
                    local->version_number);

            char *new_name = copy_string_2(*name, buf);
            free((void*)*name);
            *name = new_name;

        } else {
            report_duplicate_definition(*name, location);
            state->error = true;
        }
    }

    if (ptr) *ptr = local;
}


// Results of name resolution - list of resolved names
struct ResolveResult {
    // resolved_name is either a fully resolved global name (e.g. "pkg-name/ModName.ExportedName")
    // or a local variable name without dots (e.g. "x")
    char *resolved_name;

    // suffix is a string like "a" or "b.c"; it is present when record fields are being
    // projected from a valid object. suffix can also be NULL.
    char *suffix;

    struct ResolveResult *next;
};

static void free_resolve_result(struct ResolveResult *rr)
{
    while (rr) {
        if (rr->resolved_name) free(rr->resolved_name);
        if (rr->suffix) free(rr->suffix);
        struct ResolveResult *next = rr->next;
        free(rr);
        rr = next;
    }
}


// Tries to resolve an unqualified name as either a local, a global from the
// current module, or an imported global. Could return multiple results, if there
// is ambiguity.
// This is not usually called directly; resolve_name is usually more convenient.
static struct ResolveResult * resolve_unqualified_name(struct RenamerState *state,
                                                       const char *unqualified_name)
{
    if (strcmp(unqualified_name, "return") == 0) {
        struct ResolveResult *list = alloc(sizeof(struct ResolveResult));
        list->resolved_name = copy_string(unqualified_name);
        list->suffix = NULL;
        list->next = NULL;
        return list;
    }

    struct LocalName * local = hash_table_lookup(state->local_names, unqualified_name);

    if (local && local->scope_number != 0) {
        // local variable, currently in scope
        struct ResolveResult *list = alloc(sizeof(struct ResolveResult));
        if (local->version_number != 0) {
            char buf[30];
            sprintf(buf,
                    "@%s%" PRIu64,
                    state->match_compiler_counter ? "copy" : "",
                    local->version_number);
            list->resolved_name = copy_string_2(unqualified_name, buf);
        } else {
            list->resolved_name = copy_string(unqualified_name);
        }
        list->suffix = NULL;
        list->next = NULL;
        return list;

    } else {

        // let's see if it is a global name (from this or another module)

        struct ResolveResult *list = NULL;

        // check the current module
        if (hash_table_contains_key(state->interface_names, unqualified_name)
        || hash_table_contains_key(state->implementation_names, unqualified_name)) {
            struct ResolveResult *new_node = alloc(sizeof(struct ResolveResult));
            new_node->resolved_name = copy_string_3(state->module->name, ".", unqualified_name);
            new_node->suffix = NULL;
            new_node->next = list;
            list = new_node;
        }

        // check imports from other modules
        struct NameList *lookup = hash_table_lookup(state->imported_names, unqualified_name);
        while (lookup) {
            struct ResolveResult *new_node = alloc(sizeof(struct ResolveResult));
            new_node->resolved_name = copy_string(lookup->name);
            new_node->suffix = NULL;
            new_node->next = list;
            list = new_node;
            lookup = lookup->next;
        }

        return list;
    }
}

// Resolves a qualified name e.g. "A.B" to a global name "pkg-name/ModName.B",
// either from the current or an imported module.
// The "A" part may itself contain dots (i.e. a dotted module name) but the
// "B" part should not contain any dots.
// This is not usually called directly; resolve_name is usually more convenient.
static struct ResolveResult * resolve_qualified_name(struct RenamerState *state,
                                                     const char *A, const char *B)
{
    if (state->module && strcmp(state->module_name_without_package, A) == 0) {

        // A is our "self" module name. If B is in the interface or
        // implementation of the current module, then the result is
        // "CurrentModuleName.B", otherwise it an empty list.

        if (hash_table_contains_key(state->interface_names, B) ||
        hash_table_contains_key(state->implementation_names, B)) {
            struct ResolveResult *new_node = alloc(sizeof(struct ResolveResult));
            new_node->resolved_name = copy_string_3(state->module->name, ".", B);
            new_node->suffix = NULL;
            new_node->next = NULL;
            return new_node;
        } else {
            return NULL;
        }

    } else if (hash_table_contains_key(state->module_aliases, A)) {
        char *AB = copy_string_3(A, ".", B);
        struct NameList *list = hash_table_lookup(state->imported_names, AB);
        free(AB);

        // list should be either NULL or have one item
        if (list == NULL) {
            return NULL;
        } else if (list->next == NULL) {
            struct ResolveResult *result = alloc(sizeof(struct ResolveResult));
            result->resolved_name = copy_string(list->name);
            result->suffix = NULL;
            result->next = NULL;
            return result;
        } else {
            fatal_error("found multiple variables with the same fully-qualified name");
        }

    } else {

        // "A" was not recognised as a valid module name.
        return NULL;
    }
}

// Helper function to copy a character range [p, q).
static char * copy_char_range(const char *p, const char *q)
{
    char *result = alloc(q - p + 1);
    memcpy(result, p, q - p);
    result[q - p] = 0;
    return result;
}

// Helper function to append resolved name(s) to a list
static void add_resolve_result(struct ResolveResult **list,
                               struct ResolveResult ***tail_ptr,
                               struct ResolveResult *new_items,
                               const char *suffix)
{
    if (suffix) {
        for (struct ResolveResult *p = new_items; p; p = p->next) {
            p->suffix = copy_string(suffix);
        }
    }
    if (new_items) {
        **tail_ptr = new_items;
        *tail_ptr = &new_items->next;
        while (**tail_ptr) {
            *tail_ptr = &(**tail_ptr)->next;
        }
    }
}

// Resolves a name, calling either resolve_qualified_name or
// resolve_unqualified_name as appropriate. (Also adds "^" character
// if requested.)
static struct ResolveResult * resolve_name(struct RenamerState *state,
                                           bool requires_hat,
                                           const char *name,
                                           bool allow_suffix)
{
    struct ResolveResult *result = NULL;
    struct ResolveResult **tail_ptr = &result;

    // Find the first dot if there is one
    const char *dot = strchr(name, '.');

    // Try it as an unqualified name (possibly with a suffix)
    if (allow_suffix || dot == NULL) {
        // Split into base name and suffix
        const char *base_name = dot ? copy_char_range(name, dot) : copy_string(name);
        const char *suffix = dot ? copy_string(dot + 1) : NULL;

        // Add hat if required
        if (requires_hat) add_hat(&base_name);

        // Try to resolve as an unqualified name
        struct ResolveResult *resolved = resolve_unqualified_name(state, base_name);
        free((char*)base_name);

        // Add the results to our list
        add_resolve_result(&result, &tail_ptr, resolved, suffix);
        free((char*)suffix);

        // If there was a single result which is a local name (i.e. contains no
        // dots) then we can stop here as local names shadow all others
        if (result && !result->next && !strchr(result->resolved_name, '.')) {
            return result;
        }
    }

    // Try all possible qualified name + suffix combinations
    while (dot) {
        // Find next dot if there is one
        const char *next_dot = strchr(dot + 1, '.');

        if (allow_suffix || next_dot == NULL) {
            // Find "A", "B" and "suffix" parts of the name
            const char *A = copy_char_range(name, dot);
            const char *B = next_dot ? copy_char_range(dot + 1, next_dot) : copy_string(dot + 1);
            const char *suffix = next_dot ? copy_string(next_dot + 1) : NULL;

            // Add the hat if required
            if (requires_hat) add_hat(&B);

            // Try to resolve A.B as a qualified name
            struct ResolveResult *resolved = resolve_qualified_name(state, A, B);
            free((char*)A);
            free((char*)B);

            // Add the new resolve results to our list
            add_resolve_result(&result, &tail_ptr, resolved, suffix);
            free((char*)suffix);
        }

        // Move on
        dot = next_dot;
    }

    return result;
}

void handle_resolution_failure(struct RenamerState *state,
                               const char *name,
                               struct Location location,
                               struct ResolveResult *list)
{
    if (state->match_compiler_counter) {
        // "not in scope" errors are ignored in this mode
        if (list) fatal_error("Unexpected: non-null list in match-compiler mode");
        return;
    }

    if (list == NULL) {
        // The name didn't resolve to anything. This is a "Not in scope"
        // or another similar error.

        const char *final_dot = strrchr(name, '.');
        if (final_dot) {
            const char *A = copy_char_range(name, final_dot);

            if (hash_table_contains_key(state->module_aliases, A)
            || strcmp(A, state->module_name_without_package) == 0) {
                // "A" is a valid module-name, so the error is that
                // "A.B" is not in scope
                report_not_in_scope(location, name);

            } else {
                struct ResolveResult *list2 = resolve_name(state, false, A, true);
                if (list2) {
                    // "A" is not a module, but it is a valid name
                    // (perhaps a constant). Report that "A" is being
                    // incorrectly used as if it was a module.
                    report_incorrect_use_as_module(location, A);
                    free_resolve_result(list2);

                } else {
                    // "A" doesn't refer to anything, so we want to
                    // report "A not in scope", rather than "A.B not
                    // in scope".
                    report_not_in_scope(location, A);
                }
            }

            free((char*)A);

        } else {
            // "name" is an undotted (unqualified) name, so just
            // report "name" itself as being out of scope.
            report_not_in_scope(location, name);
        }

    } else {
        // The name could refer to multiple things, so report an ambiguity error.
        struct NameList *names = NULL;
        struct NameList **tail = &names;
        while (list) {
            struct NameList *node = alloc(sizeof(struct NameList));
            node->name = copy_string(list->resolved_name);
            node->next = NULL;
            *tail = node;
            tail = &node->next;
            list = list->next;
        }
        report_ambiguity(location, name, names);
        free_name_list(names);
    }

    state->error = true;
}


static void rename_term(struct RenamerState *state, struct Term *term);


// Type renaming.

static void * rename_var_type(void *context, struct Type *type)
{
    struct RenamerState *state = context;

    struct ResolveResult *list = resolve_name(state, true, type->var_data.name, false);
    if (list && !list->next) {
        free((char*)type->var_data.name);
        type->var_data.name = list->resolved_name;
        list->resolved_name = NULL;
    } else {
        handle_resolution_failure(state, type->var_data.name, type->location, list);
    }

    free_resolve_result(list);
    return NULL;
}

static void * rename_array(void *context, struct Type *type, void *elt_type_result)
{
    // A quirk of TypeTransform is that it does not descend into
    // the terms found in TY_ARRAY, therefore we have to do that
    // ourselves here.
    if (type->array_data.sizes != NULL) {
        for (int i = 0; i < type->array_data.ndim; ++i) {
            rename_term(context, type->array_data.sizes[i]);
        }
    }
    return NULL;
}

static void renaming_type_transform(struct TypeTransform *tr)
{
    tr->transform_var = rename_var_type;
    tr->transform_array = rename_array;
}

static void rename_type(struct RenamerState *state, struct Type *type)
{
    struct TypeTransform tr = {0};
    renaming_type_transform(&tr);
    transform_type(&tr, state, type);
}



// Term renaming.

static void apply_field_proj_suffixes(struct Term *term, const char *suffixes)
{
    if (suffixes == NULL) {
        return;
    }

    // Save the original term data
    struct Term original = *term;

    // First, count how many field names we have
    int field_count = 1;
    const char *p = suffixes;
    while ((p = strchr(p, '.')) != NULL) {
        field_count++;
        p++;
    }

    // Create an array to hold the field names
    const char **field_names = alloc(field_count * sizeof(const char *));

    // Split the suffixes string on dots
    p = suffixes;
    for (int i = 0; i < field_count; i++) {
        const char *next_dot = strchr(p, '.');
        if (next_dot == NULL) {
            // Last field name
            field_names[i] = copy_string(p);
        } else {
            // Copy the field name from p to next_dot
            field_names[i] = copy_char_range(p, next_dot);
            p = next_dot + 1;
        }
    }

    // Build the nested structure from the inside out
    struct Term *current_term = term;
    for (int i = field_count - 1; i >= 0; i--) {
        current_term->tag = TM_FIELD_PROJ;
        current_term->field_proj.lhs = alloc(sizeof(struct Term));
        current_term->field_proj.field_name = field_names[i];
        current_term->location = original.location;
        current_term->type = NULL;

        current_term = current_term->field_proj.lhs;
    }

    // The innermost "lhs" is the original term
    *current_term = original;

    free(field_names);
}

static void* rename_var_term(void *context, struct Term *term, void *type_result)
{
    struct RenamerState *state = context;

    if (strcmp(term->var.name, "return") == 0) {
        if (state->match_compiler_counter == NULL) {
            if (!state->in_postcondition) {
                report_return_var_outside_postcondition(term);
                state->error = true;
            } else if (!state->function_returns_value) {
                report_return_var_void_function(term);
                state->error = true;
            }
        }

    } else {
        struct ResolveResult *list = resolve_name(state, false, term->var.name, true);
        if (list && !list->next) {
            free((void*)term->var.name);
            term->var.name = list->resolved_name;
            list->resolved_name = NULL;
            apply_field_proj_suffixes(term, list->suffix);
        } else {
            handle_resolution_failure(state, term->var.name, term->location, list);
        }
        free_resolve_result(list);
    }

    return NULL;
}

static void* nr_rename_let(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct RenamerState *state = context;

    transform_term(tr, context, term->let.rhs);

    // open a new scope, add the variable
    ++ state->current_scope;
    struct LocalName *local;
    int old_scope;
    uint64_t old_version;
    add_new_local_name(state, term->location, &term->let.name,
                       &local, &old_scope, &old_version);

    // rename the body
    transform_term(tr, context, term->let.body);

    // remove the scope
    local->scope_number = old_scope;
    local->version_number = old_version;
    -- state->current_scope;

    return NULL;
}

static void* nr_rename_quantifier(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct RenamerState *state = context;

    transform_type(&tr->type_transform, context, term->quant.type);

    ++ state->current_scope;
    struct LocalName *local;
    int old_scope;
    uint64_t old_version;
    add_new_local_name(state, term->location, &term->quant.name,
                       &local, &old_scope, &old_version);

    transform_term(tr, context, term->quant.body);

    local->scope_number = old_scope;
    local->version_number = old_version;
    -- state->current_scope;

    return NULL;
}

struct BoundVarInfo {
    struct LocalName *local;
    int old_scope;
    uint64_t old_version;
};

// this is like add_new_local_name, but records the info in a hashtable
static void add_bound_var(struct RenamerState *state,
                          struct HashTable *bound_vars,
                          const char **name,
                          struct Location location)
{
    if (hash_table_contains_key(bound_vars, *name)) {
        report_duplicate_definition(*name, location);
        state->error = true;
        return;
    }

    struct BoundVarInfo *info = alloc(sizeof(struct BoundVarInfo));
    const char *old_name = copy_string(*name);

    add_new_local_name(state, location, name,
                       &info->local, &info->old_scope, &info->old_version);

    hash_table_insert(bound_vars, old_name, info);
}

// frees the hash table
static void unwind_bound_vars(struct HashTable *bound_vars)
{
    struct HashIterator *iter = new_hash_iterator(bound_vars);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct BoundVarInfo *info = value;
        info->local->scope_number = info->old_scope;
        info->local->version_number = info->old_version;
        free((void*)key);
        free(value);
    }
    free_hash_iterator(iter);
    free_hash_table(bound_vars);
}

static void rename_pattern(struct RenamerState *state,
                           struct HashTable *bound_vars,
                           struct Pattern *pattern)
{
    switch (pattern->tag) {
    case PAT_VAR:
        add_bound_var(state, bound_vars, &pattern->var.name, pattern->location);
        break;

    case PAT_BOOL:
    case PAT_INT:
        break;

    case PAT_RECORD:
        for (struct NamePatternList *node = pattern->record.fields; node; node = node->next) {
            rename_pattern(state, bound_vars, node->pattern);
        }
        break;

    case PAT_VARIANT:
        if (pattern->variant.payload) {
            rename_pattern(state, bound_vars, pattern->variant.payload);
        }

        struct ResolveResult *list = resolve_name(state, false, pattern->variant.variant_name, false);
        if (list && !list->next) {
            free((void*)pattern->variant.variant_name);
            pattern->variant.variant_name = list->resolved_name;
            list->resolved_name = NULL;
        } else {
            handle_resolution_failure(state, pattern->variant.variant_name, pattern->location, list);
        }

        free_resolve_result(list);
        break;

    case PAT_WILDCARD:
        break;
    }
}

static void* nr_rename_match(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct RenamerState *state = context;

    transform_term(tr, context, term->match.scrutinee);

    for (struct Arm *arm = term->match.arms; arm; arm = arm->next) {

        ++ state->current_scope;
        struct HashTable *bound_vars = new_hash_table();

        // this will add the pattern-bound variables into scope
        rename_pattern(state, bound_vars, arm->pattern);

        // this will rename all the variables in the rhs term
        transform_term(tr, context, arm->rhs);

        // this will pop the variables out of scope again (and free bound_vars)
        unwind_bound_vars(bound_vars);
        -- state->current_scope;
    }

    return NULL;
}

static void rename_term(struct RenamerState *state, struct Term *term)
{
    struct TermTransform tr;
    memset(&tr, 0, sizeof(tr));
    tr.transform_var = rename_var_term;
    tr.nr_transform_let = nr_rename_let;
    tr.nr_transform_quantifier = nr_rename_quantifier;
    tr.nr_transform_match = nr_rename_match;
    renaming_type_transform(&tr.type_transform);
    transform_term(&tr, state, term);
}


// Renames an entire list of Attributes
static void rename_attributes(struct RenamerState *state, struct Attribute *attr)
{
    while (attr) {
        switch (attr->tag) {
        case ATTR_REQUIRES:
        case ATTR_ENSURES:
        case ATTR_INVARIANT:
        case ATTR_DECREASES:

            if (attr->tag == ATTR_ENSURES) {
                state->in_postcondition = true;
            }

            rename_term(state, attr->term);

            state->in_postcondition = false;

            break;
        }

        attr = attr->next;
    }
}

// Renames an entire list of Statements
static void rename_statement(struct RenamerState *state, struct Statement *stmt)
{
    struct LocalName *local;
    int old_scope;
    uint64_t old_version;

    while (stmt) {
        switch (stmt->tag) {
        case ST_VAR_DECL:
            rename_type(state, stmt->var_decl.type);
            rename_term(state, stmt->var_decl.rhs);

            add_new_local_name(state, stmt->location, &stmt->var_decl.name,
                               &local, &old_scope, &old_version);

            rename_statement(state, stmt->next);
            local->scope_number = old_scope;
            local->version_number = old_version;

            return;

        case ST_FIX:
            rename_type(state, stmt->fix.type);

            add_new_local_name(state, stmt->location, &stmt->fix.name,
                               &local, &old_scope, &old_version);

            rename_statement(state, stmt->next);
            local->scope_number = old_scope;
            local->version_number = old_version;

            return;

        case ST_OBTAIN:
            rename_type(state, stmt->obtain.type);

            add_new_local_name(state, stmt->location, &stmt->obtain.name,
                               &local, &old_scope, &old_version);
            rename_term(state, stmt->obtain.condition);

            rename_statement(state, stmt->next);
            local->scope_number = old_scope;
            local->version_number = old_version;

            return;

        case ST_USE:
            rename_term(state, stmt->use.term);
            break;

        case ST_ASSIGN:
            rename_term(state, stmt->assign.lhs);
            rename_term(state, stmt->assign.rhs);
            break;

        case ST_SWAP:
            rename_term(state, stmt->swap.lhs);
            rename_term(state, stmt->swap.rhs);
            break;

        case ST_RETURN:
            if (stmt->ret.value) {
                rename_term(state, stmt->ret.value);
            }
            break;

        case ST_ASSERT:
            rename_term(state, stmt->assert_data.condition);

            ++ state->current_scope;
            rename_statement(state, stmt->assert_data.proof);
            -- state->current_scope;

            break;

        case ST_ASSUME:
            rename_term(state, stmt->assume.condition);
            break;

        case ST_IF:
            rename_term(state, stmt->if_data.condition);

            ++ state->current_scope;
            rename_statement(state, stmt->if_data.then_block);
            rename_statement(state, stmt->if_data.else_block);
            -- state->current_scope;

            break;

        case ST_WHILE:
            rename_term(state, stmt->while_data.condition);

            rename_attributes(state, stmt->while_data.attributes);

            ++ state->current_scope;
            rename_statement(state, stmt->while_data.body);
            -- state->current_scope;

            break;

        case ST_CALL:
            rename_term(state, stmt->call.term);
            break;

        case ST_MATCH:
            rename_term(state, stmt->match.scrutinee);

            for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {
                ++ state->current_scope;
                struct HashTable *bound_vars = new_hash_table();

                // this will add the pattern-bound variables into scope
                rename_pattern(state, bound_vars, arm->pattern);

                // this will rename all the variables in the rhs term
                rename_statement(state, arm->rhs);

                // this will pop the variables out of scope again (and free bound_vars)
                unwind_bound_vars(bound_vars);
                -- state->current_scope;
            }
            break;

        case ST_MATCH_FAILURE:
            break;

        case ST_SHOW_HIDE:
            {
                struct ResolveResult *list = resolve_name(state, false, stmt->show_hide.name, false);
                if (list && !list->next) {
                    free((void*)stmt->show_hide.name);
                    stmt->show_hide.name = list->resolved_name;
                    list->resolved_name = NULL;
                } else {
                    handle_resolution_failure(state, stmt->show_hide.name, stmt->location, list);
                }
                free_resolve_result(list);
            }
            break;
        }

        stmt = stmt->next;
    }
}


static void rename_const_decl(struct RenamerState *state, struct Decl *decl)
{
    if (decl->const_data.type) {
        rename_type(state, decl->const_data.type);
    }

    if (decl->const_data.rhs) {
        rename_term(state, decl->const_data.rhs);
    }
}

static void rename_function_decl(struct RenamerState *state, struct Decl *decl)
{
    for (struct TyVarList *tyvar = decl->function_data.tyvars; tyvar; tyvar = tyvar->next) {
        add_hat(&tyvar->name);
        add_new_local_name(state, decl->location, &tyvar->name, NULL, NULL, NULL);
    }

    for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
        add_new_local_name(state, decl->location, &arg->name, NULL, NULL, NULL);
        rename_type(state, arg->type);
    }

    if (decl->function_data.return_type) {
        rename_type(state, decl->function_data.return_type);
        state->function_returns_value = true;
    }

    rename_attributes(state, decl->attributes);
    rename_statement(state, decl->function_data.body);

    state->function_returns_value = false;
}

static void rename_datatype_decl(struct RenamerState *state, struct Decl *decl)
{
    for (struct TyVarList *tyvar = decl->datatype_data.tyvars; tyvar; tyvar = tyvar->next) {
        add_hat(&tyvar->name);
        add_new_local_name(state, decl->location, &tyvar->name, NULL, NULL, NULL);
    }

    for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
        // rename the data ctor name itself
        char *new_name = copy_string_3(state->module->name, ".", ctor->name);
        free((char*)ctor->name);
        ctor->name = new_name;

        // rename the payload type
        rename_type(state, ctor->payload);
    }
}

static void rename_typedef_decl(struct RenamerState *state, struct Decl *decl)
{
    for (struct TyVarList *tyvar = decl->typedef_data.tyvars; tyvar; tyvar = tyvar->next) {
        add_hat(&tyvar->name);
        add_new_local_name(state, decl->location, &tyvar->name, NULL, NULL, NULL);
    }

    rename_type(state, decl->typedef_data.rhs);
}

// Rename all the local names in a single Decl
static void rename_one_decl(struct RenamerState *state, struct Decl *decl)
{
    reset_local_names(state);

    if (decl->name == NULL) {
        // this decl was subject to a "duplicate definition" error,
        // do not try to process it further
        return;
    }

    const char *new_name = copy_string_3(state->module->name, ".", decl->name);
    free((char*)decl->name);
    decl->name = new_name;

    switch (decl->tag) {
    case DECL_CONST:
        rename_const_decl(state, decl);
        break;

    case DECL_FUNCTION:
        rename_function_decl(state, decl);
        break;

    case DECL_DATATYPE:
        rename_datatype_decl(state, decl);
        break;

    case DECL_TYPEDEF:
        rename_typedef_decl(state, decl);
        break;
    }
}

static bool add_new_global_name(struct RenamerState *state,
                                bool interface,
                                const char *name,   // shared with AST
                                const struct Location *location)
{
    struct HashTable *hash_table;
    if (interface) {
        hash_table = state->interface_names;
    } else {
        hash_table = state->implementation_names;
    }

    if (hash_table_contains_key(hash_table, name)) {
        report_duplicate_definition(name, *location);
        state->error = true;
        return false;
    } else {
        hash_table_insert(hash_table, copy_string(name), NULL);
        return true;
    }
}

// Rename a list of Decls (adding them into scope)
static void rename_decls(struct RenamerState *state,
                         struct Decl *decls,
                         bool interface)
{
    // First, add all the global names to our hash table
    for (struct Decl *decl = decls; decl; decl = decl->next) {

        switch (decl->tag) {
        case DECL_CONST:
        case DECL_FUNCTION:
            break;

        case DECL_DATATYPE:
            // For datatypes, we want to add "^" to the name, and also add the data
            // constructors themselves as global names
            add_hat(&decl->name);
            for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
                add_new_global_name(state, interface, ctor->name, &ctor->location);
            }
            break;

        case DECL_TYPEDEF:
            add_hat(&decl->name);
            break;
        }

        // Now add the decl name itself as a global name
        if (!add_new_global_name(state, interface, decl->name, &decl->location)) {
            // Error - NULL out the name to prevent further errors with this decl
            free((void*)decl->name);
            decl->name = NULL;
        }

    }

    // Now rename the local names in each decl
    for (struct Decl *decl = decls; decl; decl = decl->next) {
        rename_one_decl(state, decl);
    }
}

// Resolve imports i.e. change "import ModName;" into "import package-name/ModName;".
static void resolve_imports(struct PackageLoader *package_loader,
                            const char *my_package_name,
                            struct Import *import)
{
    while (import) {
        struct ModulePathInfo *info = find_module(package_loader, my_package_name, import->module_name);
        if (info == NULL) {
            // This is unexpected because we should already have
            // loaded (and renamed) any imported modules before we get
            // to this point
            fatal_error("resolve_imports failed");
        }
        char *new_name = copy_string_3(info->package_name, "/", import->module_name);
        free((char*)import->module_name);
        import->module_name = new_name;
        import = import->next;
    }
}

// Helper for add_one_import.
static void insert_import(struct RenamerState *state, const char *name, const char *maps_to)
{
    struct NameList *existing = hash_table_lookup(state->imported_names, name);

    // If this mapping already exists then skip adding it
    for (struct NameList *search = existing; search; search = search->next) {
        if (strcmp(search->name, maps_to) == 0) {
            return;
        }
    }

    // Add the new mapping
    struct NameList *node = alloc(sizeof(struct NameList));
    node->name = copy_string(maps_to);
    node->next = existing;
    hash_table_insert(state->imported_names, existing ? name : copy_string(name), node);
}

// Helper for add_imports_to_scope.
static void add_one_import(struct RenamerState *state, struct Import *import)
{
    hash_table_insert(state->module_aliases, import->alias_name, NULL);

    struct NameList *list = hash_table_lookup(state->renamer_env, import->module_name);
    while (list) {
        const char *import_name = copy_string_3(import->alias_name, ".", list->name);
        const char *real_name = copy_string_3(import->module_name, ".", list->name);

        if (!import->qualified) {
            insert_import(state, list->name, real_name);
        }

        insert_import(state, import_name, real_name);

        free((char*)import_name);
        free((char*)real_name);

        list = list->next;
    }
}

// Add the imports to module_aliases and imported_names.
static void add_imports_to_scope(struct RenamerState *state, struct Import *imports)
{
    for (struct Import *import = imports; import; import = import->next) {
        if (strcmp(import->alias_name, state->module_name_without_package) == 0) {
            report_import_clash_with_current(import);
            state->error = true;
        } else if (hash_table_contains_key(state->module_aliases, import->alias_name)) {
            report_duplicate_import(import);
            state->error = true;
        } else {
            add_one_import(state, import);
        }
    }
}

// Add all the exported names from this module into the renamer_env.
static void add_exported_names(struct RenamerState *state)
{
    if (hash_table_contains_key(state->renamer_env, state->module->name)) {
        fatal_error("unexpected - module already exists");
    }

    struct NameList *list = NULL;

    struct HashIterator *iter = new_hash_iterator(state->interface_names);
    const char *exported_name;
    void *dummy_value;
    while (hash_iterator_next(iter, &exported_name, &dummy_value)) {
        struct NameList *node = alloc(sizeof(struct NameList));
        node->name = copy_string(exported_name);
        node->next = list;
        list = node;
    }
    free_hash_iterator(iter);

    hash_table_insert(state->renamer_env, copy_string(state->module->name), list);
}

bool rename_module(struct HashTable *renamer_env,
                   struct PackageLoader *package_loader,
                   const char *package_name,
                   struct Module *module,
                   bool interface_only)
{
    struct RenamerState state;
    init_renamer_state(&state);
    state.renamer_env = renamer_env;
    state.module = module;
    state.module_name_without_package = copy_string(module->name);

    char *new_name = copy_string_3(package_name, "/", module->name);
    free((char*)module->name);
    module->name = new_name;

    resolve_imports(package_loader, package_name, module->interface_imports);
    add_imports_to_scope(&state, module->interface_imports);

    if (module->interface) {
        rename_decls(&state, module->interface->decl, true);
    }

    if (!interface_only) {
        resolve_imports(package_loader, package_name, module->implementation_imports);
        add_imports_to_scope(&state, module->implementation_imports);

        if (module->implementation) {
            rename_decls(&state, module->implementation->decl, false);
        }
    }

    add_exported_names(&state);

    clean_up_renamer_state(&state);

    return !state.error;
}

void rename_term_for_match_compiler(struct Term *term, uint64_t * name_counter)
{
    struct RenamerState state;
    init_renamer_state(&state);
    state.match_compiler_counter = name_counter;

    rename_term(&state, term);

    clean_up_renamer_state(&state);
}

void rename_statement_for_match_compiler(struct Statement *stmt, uint64_t * name_counter)
{
    struct RenamerState state;
    init_renamer_state(&state);
    state.match_compiler_counter = name_counter;

    rename_statement(&state, stmt);

    clean_up_renamer_state(&state);
}
