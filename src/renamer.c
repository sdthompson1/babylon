/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "hash_table.h"
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
    // Key = module name (allocated)
    // Value = NameList of (unqualified) names exported by this module.
    struct HashTable *renamer_env;

    // Information about the current module
    struct Module *module;
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
    // Key = name (qualified or unqualified) (allocated)
    // Value = NameList of qualified names that it can resolve to (allocated)
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


// Tries to resolve an unqualified name as either a local, global from the
// current module, or imported global. Could return multiple results, if there
// is ambiguity.
static struct NameList * resolve_unqualified_name(struct RenamerState *state,
                                                  const char *unqualified_name)
{
    if (strcmp(unqualified_name, "return") == 0) {
        struct NameList *list = alloc(sizeof(struct NameList));
        list->name = copy_string(unqualified_name);
        list->next = NULL;
        return list;
    }

    struct LocalName * local = hash_table_lookup(state->local_names, unqualified_name);

    if (local && local->scope_number != 0) {
        // local variable, currently in scope
        struct NameList *list = alloc(sizeof(struct NameList));
        if (local->version_number != 0) {
            char buf[30];
            sprintf(buf,
                    "@%s%" PRIu64,
                    state->match_compiler_counter ? "copy" : "",
                    local->version_number);
            list->name = copy_string_2(unqualified_name, buf);
        } else {
            list->name = copy_string(unqualified_name);
        }
        list->next = NULL;
        return list;

    } else {

        // let's see if it is a global name (from this or another module)

        struct NameList *list = NULL;

        // check the current module
        if (hash_table_contains_key(state->interface_names, unqualified_name)
        || hash_table_contains_key(state->implementation_names, unqualified_name)) {
            struct NameList *new_node = alloc(sizeof(struct NameList));
            new_node->name = copy_string_3(state->module->name, ".", unqualified_name);
            new_node->next = list;
            list = new_node;
        }

        // check imports from other modules
        struct NameList *lookup = hash_table_lookup(state->imported_names, unqualified_name);
        while (lookup) {
            struct NameList *new_node = alloc(sizeof(struct NameList));
            new_node->name = copy_string(lookup->name);
            new_node->next = list;
            list = new_node;
            lookup = lookup->next;
        }

        return list;
    }
}


// Resolves a qualified name "A.B" to a global name, either from the
// current or an imported module.
static struct NameList * resolve_qualified_name(struct RenamerState *state,
                                                const char *A, const char *B)
{
    if (state->module && strcmp(state->module->name, A) == 0) {

        // A is our "self" module name. If B is in the interface or
        // implementation of the current module, then the result is
        // "A.B", otherwise it an empty list.

        if (hash_table_contains_key(state->interface_names, B) ||
        hash_table_contains_key(state->implementation_names, B)) {
            struct NameList *new_node = alloc(sizeof(struct NameList));
            new_node->name = copy_string_3(A, ".", B);
            new_node->next = NULL;
            return new_node;
        } else {
            return NULL;
        }

    } else if (hash_table_contains_key(state->module_aliases, A)) {
        char *AB = copy_string_3(A, ".", B);
        struct NameList *list = hash_table_lookup(state->imported_names, AB);
        free(AB);
        return copy_name_list(list);  // list should either be NULL or have one item.

    } else {

        // "A" was not recognised as a valid module name.
        return NULL;
    }
}


static bool split_on_dot(const char *name, const char **A, const char **B)
{
    const char *dot = strchr(name, '.');
    if (dot) {
        size_t len = dot - name;

        char *new_a = malloc(len + 1);
        memcpy(new_a, name, len);
        new_a[len] = 0;
        *A = new_a;

        *B = copy_string(dot + 1);

        return true;

    } else {
        return false;
    }
}


// Resolves a name, calling either resolve_qualified_name or
// resolve_unqualified_name as appropriate. (Also adds "^" character
// if requested.)
static struct NameList * resolve_name(struct RenamerState *state,
                                      bool requires_hat,
                                      const char *name)
{
    // Qualified names
    const char *A;
    const char *B;
    if (split_on_dot(name, &A, &B)) {
        if (requires_hat) add_hat(&B);
        struct NameList *result = resolve_qualified_name(state, A, B);
        free((char*)A);
        free((char*)B);
        return result;
    }

    // Unqualified names
    const char *name_copy = copy_string(name);
    if (requires_hat) add_hat(&name_copy);
    struct NameList *result = resolve_unqualified_name(state, name_copy);
    free((char*)name_copy);
    return result;
}

void handle_resolution_failure(struct RenamerState *state,
                               const char *name,
                               struct Location location,
                               struct NameList *list)
{
    if (state->match_compiler_counter) {
        // "not in scope" errors are ignored in this mode
        if (list) fatal_error("Unexpected: non-null list in match-compiler mode");
        return;
    }

    if (list == NULL) {
        // The name didn't resolve to anything. This is a "Not in
        // scope" or another similar error.

        const char *A;
        const char *B;
        if (split_on_dot(name, &A, &B)) {

            if (hash_table_contains_key(state->module_aliases, A)
            || strcmp(A, state->module->name) == 0) {
                // "A" is a valid module-name, so we can't say that "A
                // is not in scope". But the module doesn't export
                // "B", so saying "A.B not in scope" is valid.
                report_not_in_scope(location, name);

            } else {
                struct NameList *list2 = resolve_name(state, false, A);
                if (list2) {
                    // "A" is not a module, but is a valid name
                    // (perhaps it is a type, or constant). Report
                    // that "A" is being incorrectly used as if it
                    // were a module.
                    report_incorrect_use_as_module(location, A);
                    free_name_list(list2);

                } else {
                    // "A" doesn't refer to anything, so we want to
                    // report "A not in scope" (rather than "A.B not
                    // in scope").
                    report_not_in_scope(location, A);
                }
            }
            free((char*)A);
            free((char*)B);

        } else {
            // "name" is an undotted (unqualified) name, so just
            // report "name" itself as being out of scope.
            report_not_in_scope(location, name);
        }

    } else {
        // The name could refer to multiple things so report an ambiguity error
        report_ambiguity(location, name, list);
    }

    state->error = true;
}


// Type renaming.

static void * rename_var_type(void *context, struct Type *type)
{
    struct RenamerState *state = context;

    struct NameList *list = resolve_name(state, true, type->var_data.name);
    if (list && !list->next) {
        free((char*)type->var_data.name);
        type->var_data.name = list->name;
        list->name = NULL;
    } else {
        handle_resolution_failure(state, type->var_data.name, type->location, list);
    }

    free_name_list(list);
    return NULL;
}

static void renaming_type_transform(struct TypeTransform *tr)
{
    tr->transform_var = rename_var_type;
}

static void rename_type(struct RenamerState *state, struct Type *type)
{
    struct TypeTransform tr = {0};
    renaming_type_transform(&tr);
    transform_type(&tr, state, type);
}



// Term renaming.

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
        struct NameList *list = resolve_name(state, false, term->var.name);
        if (list && !list->next) {
            free((void*)term->var.name);
            term->var.name = list->name;
            list->name = NULL;
        } else {
            handle_resolution_failure(state, term->var.name, term->location, list);
        }
        free_name_list(list);
    }

    return NULL;
}

// Appends ".B" to all names in unqual_list, concatenates the two
// lists, returns the result. The original lists are both handed over.
// It's assumed that qual_list is not empty.
static struct NameList * combine_qual_unqual_lists(struct NameList *qual_list,
                                                   struct NameList *unqual_list,
                                                   const char *B)
{
    struct NameList *ptr = qual_list;
    while (ptr->next) ptr = ptr->next;
    ptr->next = unqual_list;
    ptr = unqual_list;

    while (ptr) {
        char *new_name = copy_string_3(ptr->name, ".", B);
        free((char*)ptr->name);
        ptr->name = new_name;
        ptr = ptr->next;
    }

    return qual_list;
}
                                         
static void* nr_rename_field_proj(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct RenamerState *state = context;

    if (state->match_compiler_counter == NULL
    && term->field_proj.lhs->tag == TM_VAR) {

        // Term is of the form "A.B" where A and B are names
        // (and we are not in match-compiler mode).

        // This could be either a qualified name "A.B", or a
        // projection of field "B" from the unqualified name "A". We
        // will try both possibilities.

        const char * A = term->field_proj.lhs->var.name;
        const char * B = term->field_proj.field_name;
        struct NameList *qual_list = resolve_qualified_name(state, A, B);
        struct NameList *unqual_list = resolve_unqualified_name(state, A);

        if (unqual_list && !unqual_list->next && strchr(unqual_list->name, '.') == NULL) {
            // "A" resolves to a local name (and then "B" is a field
            // name of a record).

            // This shadows all other interpretations including "A"
            // being a global, or "A.B" being a qualified reference to
            // a global.

        } else if (qual_list) {
            // "A.B" can be interpreted as a qualified reference to a
            // global.

            // Consider also whether A could be an unqualified
            // reference to a global (with B a field name).

            // If this ends up with more than one possible
            // interpretation, then we have an ambiguity error.
            // Otherwise the (unique) correct interpretation is that
            // "A.B" is a qualified name of a global.

            struct NameList *combined_list = combine_qual_unqual_lists(qual_list, unqual_list, B);
            qual_list = unqual_list = NULL;

            if (combined_list->next) {
                // Ambiguity error.
                char *AB = copy_string_3(A, ".", B);
                handle_resolution_failure(state, AB, term->location, combined_list);
                free(AB);

            } else {
                // Change the term into a TM_VAR (with a qualified name).

                free_term(term->field_proj.lhs);
                free((char*)term->field_proj.field_name);

                term->tag = TM_VAR;
                term->var.name = combined_list->name;
                combined_list->name = NULL;
                term->var.postcond_new = false;  // "new" not applicable to imported names
            }

            free_name_list(combined_list);
            return NULL;

        } else if (unqual_list && !unqual_list->next) {
            // We have a unique interpretation where "A" is an
            // unqualified global, and B is a field-name.

        } else {
            // Either there are multiple interpretations where "A" is
            // an unqualified global, or there are no possible
            // interpretations of either "A" or "A.B".
            char *AB = copy_string_3(A, ".", B);
            handle_resolution_failure(state, AB, term->location, unqual_list);
            free(AB);
            free_name_list(qual_list);
            free_name_list(unqual_list);
            return NULL;
        }

        free_name_list(qual_list);
        free_name_list(unqual_list);
    }

    // If we get here, we want to continue renaming the LHS term in
    // its own right.
    transform_term(tr, context, term->field_proj.lhs);
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

        struct NameList *list = resolve_name(state, false, pattern->variant.variant_name);
        if (list && !list->next) {
            free((void*)pattern->variant.variant_name);
            pattern->variant.variant_name = list->name;
            list->name = NULL;
        } else {
            handle_resolution_failure(state, pattern->variant.variant_name, pattern->location, list);
        }

        free_name_list(list);
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
    tr.nr_transform_field_proj = nr_rename_field_proj;
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
                struct NameList *list = resolve_name(state, false, stmt->show_hide.name);
                if (list && !list->next) {
                    free((void*)stmt->show_hide.name);
                    stmt->show_hide.name = list->name;
                    list->name = NULL;
                } else {
                    handle_resolution_failure(state, stmt->show_hide.name, stmt->location, list);
                }
                free_name_list(list);
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


// Helper for add_one_import.
static void insert_import(struct RenamerState *state, const char *name, const char *maps_to)
{
    struct NameList *existing = hash_table_lookup(state->imported_names, name);
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
        if (strcmp(import->alias_name, state->module->name) == 0) {
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

bool rename_module(struct HashTable *renamer_env, struct Module *module, bool interface_only)
{
    struct RenamerState state;
    init_renamer_state(&state);
    state.renamer_env = renamer_env;
    state.module = module;

    add_imports_to_scope(&state, module->interface_imports);

    if (module->interface) {
        rename_decls(&state, module->interface->decl, true);
    }

    add_imports_to_scope(&state, module->implementation_imports);

    if (module->implementation) {
        rename_decls(&state, module->implementation->decl, false);
    }

    add_exported_names(&state);

    clean_up_renamer_state(&state);

    // Imports are no longer needed after renaming
    free_import(module->interface_imports);
    free_import(module->implementation_imports);
    module->interface_imports = NULL;
    module->implementation_imports = NULL;

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
