/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "eval_const.h"
#include "match_compiler.h"
#include "names.h"
#include "remove_univars.h"
#include "stacked_hash_table.h"
#include "subst_type.h"
#include "typechecker.h"
#include "util.h"

#include <ctype.h>
#include <inttypes.h>
#include <limits.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_FIELD_NUM 1000000

// ----------------------------------------------------------------------------------------------------

// typechecker context
struct TypecheckContext {
    // Type environment
    TypeEnv *type_env;

    // True if at least one type error has been detected
    bool error;

    // True if we are in executable code
    bool executable;

    // True if the current function is marked "impure"
    bool impure;

    // True if we are at the "top level scope" of a proof
    bool at_proof_top_level;

    // True if we are in a postcondition
    bool postcondition;

    // Pointer to the current statement being checked (if any)
    struct Statement *statement;

    // Pointer to (a sub-term of) the assert term currently being checked, if any
    struct Term *assert_term;

    // Counter for temporary names
    uint64_t temp_name_counter;
};

static struct TypeEnvEntry * lookup_type_info(const struct TypecheckContext *context, const char *name)
{
    return stacked_hash_table_lookup(context->type_env, name);
}

struct TypeEnvEntry * type_env_lookup(const TypeEnv *env, const char *name)
{
    return stacked_hash_table_lookup(env, name);
}

static void free_type_env_entry(struct TypeEnvEntry *entry)
{
    free_type(entry->type);
    free_term(entry->value);
    free(entry);
}

static void remove_from_type_env_hash_table(struct HashTable *table, const char *name)
{
    const char *key;
    void *value;
    hash_table_lookup_2(table, name, &key, &value);
    if (key) {
        hash_table_remove(table, key);
        free_type_env_entry(value);
        free((char*)key);
    }
}

void add_to_type_env(TypeEnv *env,
                     const char *name,    // copied
                     struct Type *type,   // handed over
                     bool ghost,
                     bool read_only,
                     bool constructor,
                     bool impure)
{
    remove_from_type_env_hash_table(env->table, name);   // just in case there is an existing entry

    struct TypeEnvEntry *entry = alloc(sizeof(struct TypeEnvEntry));
    entry->type = type;
    entry->value = NULL;
    entry->ghost = ghost;
    entry->read_only = read_only;
    entry->constructor = constructor;
    entry->impure = impure;

    // add to the topmost HashTable in the stack
    hash_table_insert(env->table, copy_string(name), entry);
}

static void free_type_env_key_and_value(void *context, const char *key, void *value)
{
    free((char*)key);
    free_type_env_entry(value);
}

TypeEnv * new_type_env()
{
    TypeEnv * env = alloc(sizeof(TypeEnv));
    env->table = new_hash_table();
    env->base = NULL;
    return env;
}

TypeEnv * push_type_env(TypeEnv *env)
{
    TypeEnv * new_env = new_type_env();
    new_env->base = env;
    return new_env;
}

TypeEnv * pop_type_env(TypeEnv *env)
{
    hash_table_for_each(env->table, free_type_env_key_and_value, NULL);
    free_hash_table(env->table);
    TypeEnv *prev = env->base;
    free(env);
    return prev;
}

TypeEnv * collapse_type_env(TypeEnv *env)
{
    stacked_hash_table_collapse(env, NULL, free_type_env_key_and_value);
    return pop_type_env(env);
}

void free_type_env(TypeEnv *env)
{
    while (env) {
        env = pop_type_env(env);
    }
}


// ----------------------------------------------------------------------------------------------------

// Functions needed by kind checking.

static void typecheck_term(struct TypecheckContext *tc_context, struct Term *term);

static bool match_term_to_type(struct TypecheckContext *tc_context,
                               struct Type *expected_type,
                               struct Term **term);

static bool ensure_type_meets_flags(struct TypecheckContext *tc_context,
                                    struct UnivarNode *node,
                                    struct Type *type,
                                    const struct Location *loc);

// ----------------------------------------------------------------------------------------------------

// Kind-checking of types.

// Kind-checking is intended to run on Types created by the parser. It
// does several things:

//  1) Any TY_VAR nodes representing datatypes or typedefs are removed
//     and replaced with their underlying type (this may be a
//     TY_LAMBDA type if the datatype/typedef has type-variables).

//  2) Any TY_RECORD types (representing tuple types) will have
//     numeric field names inserted.

//  3) In the case of types of kind *, all TY_LAMBDA and TY_APP nodes
//     are removed (by beta-reduction). In the case of higher-kinded
//     types, there may still be a single TY_LAMBDA node at the top
//     level, but there should be no other TY_LAMBDA or TY_APP nodes.

//  4) Any errors (such as failing to provide required type arguments)
//     are reported.

//  5) The sizes of fixed-size arrays will be normalised to
//     TM_INT_LITERAL.


// This can be applied to types of kind *. Returns true on success.
// It may free and reallocate the Type.
static bool kindcheck_type(struct TypecheckContext *tc_context, struct Type **type);


// This can be applied to types of kind (*,*,...,*) -> *, for any
// number of *'s (including zero) on the left-hand side. It does
// NOT check if the type is executable (even if tc_context->executable
// is true). Otherwise it behaves like kindcheck_type.
static bool kindcheck_type_constructor(struct TypecheckContext *tc_context, struct Type **type);



const char * field_num_to_string(int field_num)
{
    if (field_num > MAX_FIELD_NUM) {
        fatal_error("Too many fields!");
    }
    char str[20];
    sprintf(str, "%d", field_num);
    return copy_string(str);
}

static bool kindcheck_type_constructor(struct TypecheckContext *tc_context, struct Type **type)
{
    switch ((*type)->tag) {
    case TY_VAR:
        {
            struct TypeEnvEntry *entry = lookup_type_info(tc_context, (*type)->var_data.name);
            if (entry) {  // note: entry==NULL probably means there was a previous error
                if (entry->type != NULL) {
                    // expand out datatype or typedef
                    struct Location loc = (*type)->location;
                    free_type(*type);
                    *type = copy_type(entry->type);
                    (*type)->location = loc;  // preserve original location for error messages
                }
            }
        }
        return true;

    case TY_BOOL:
    case TY_FINITE_INT:
    case TY_MATH_INT:
    case TY_MATH_REAL:
        // nothing to do
        return true;

    case TY_RECORD:
        {
            // first pass: number the positional fields,
            // and check for mixed positional and named fields
            bool found_number = false;
            bool found_name = false;
            int field_num = 0;
            for (struct NameTypeList *field = (*type)->record_data.fields; field; field = field->next) {
                if (field->name == NULL) {
                    found_number = true;
                    field->name = field_num_to_string(field_num++);
                } else {
                    found_name = true;
                }
            }
            if (found_number && found_name) {
                report_mixed_positional_and_named_fields((*type)->location);
                tc_context->error = true;
                return false;
            }

            // second pass: check kinds, and check for duplicate fieldnames
            bool ok = true;

            struct HashTable *found_field_names = new_hash_table();

            for (struct NameTypeList *field = (*type)->record_data.fields; field; field = field->next) {
                if (!kindcheck_type(tc_context, &field->type)) {
                    ok = false;
                }

                if (hash_table_contains_key(found_field_names, field->name)) {
                    report_duplicate_field_name((*type)->location, field->name);
                    tc_context->error = true;
                    ok = false;
                }

                hash_table_insert(found_field_names, field->name, NULL);
            }

            free_hash_table(found_field_names);

            return ok;
        }

    case TY_ARRAY:
        if (!kindcheck_type(tc_context, &(*type)->array_data.element_type)) {
            return false;
        }

        if ((*type)->array_data.sizes) {
            // Array sizes are u64
            struct Type *u64 = make_int_type(g_no_location, false, 64);

            for (int i = 0; i < (*type)->array_data.ndim; ++i) {
                typecheck_term(tc_context, (*type)->array_data.sizes[i]);
                if ((*type)->array_data.sizes[i]->type == NULL) {
                    // Size doesn't typecheck
                    free_type(u64);
                    return false;
                }

                if (!match_term_to_type(tc_context, u64, &(*type)->array_data.sizes[i])) {
                    // Size doesn't have type u64
                    free_type(u64);
                    return false;
                }

                struct Term *normal = eval_to_normal_form(tc_context->type_env, (*type)->array_data.sizes[i]);
                if (normal == NULL) {
                    // Size is not a compile time constant
                    free_type(u64);
                    return false;
                }
                free_term((*type)->array_data.sizes[i]);
                (*type)->array_data.sizes[i] = normal;
            }

            free_type(u64);
        }

        return true;

    case TY_UNIVAR:
    case TY_VARIANT:
    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
        // these are not directly created by the parser so we shouldn't ever need to resolve them
        fatal_error("unreachable code");

    case TY_APP:
        {
            bool ok = true;

            // kindcheck the lhs
            if (!kindcheck_type_constructor(tc_context, &(*type)->app_data.lhs)) {
                ok = false;
            }

            // check correct number of tyargs
            if (ok) {
                int num_exp_tyargs = 0;
                int num_act_tyargs = type_list_length((*type)->app_data.tyargs);

                if ((*type)->app_data.lhs->tag == TY_LAMBDA) {
                    num_exp_tyargs = tyvar_list_length((*type)->app_data.lhs->lambda_data.tyvars);
                }

                if (num_exp_tyargs != num_act_tyargs) {
                    report_wrong_number_of_type_arguments((*type)->location, num_exp_tyargs, num_act_tyargs);
                    tc_context->error = true;
                    ok = false;
                }
            }

            // kindcheck each tyarg
            for (struct TypeList *node = (*type)->app_data.tyargs; node; node = node->next) {
                // the tyargs should be proper types (not type constructors)
                if (!kindcheck_type(tc_context, &node->type)) {
                    ok = false;
                }
            }

            if (!ok) {
                return false;
            }

            // substitute the args into the lhs type.
            struct Type *new_type =
                substitute_in_type_from_list((*type)->app_data.lhs->lambda_data.tyvars,
                                             (*type)->app_data.tyargs,
                                             (*type)->app_data.lhs->lambda_data.type);
            new_type->location = (*type)->location;  // preserve the TY_APP's location for error messages
            free_type(*type);
            *type = new_type;
            return true;
        }
        break;
    }

    fatal_error("resolve_type_constructor: invalid type tag");
}

static bool kindcheck_type(struct TypecheckContext *tc_context, struct Type **type)
{
    if (!kindcheck_type_constructor(tc_context, type)) {
        return false;
    }

    if ((*type)->tag == TY_LAMBDA) {
        // error, this is a valid type constructor, but not a proper type
        // (it's missing its type arguments)
        report_wrong_number_of_type_arguments((*type)->location, tyvar_list_length((*type)->lambda_data.tyvars), 0);
        tc_context->error = true;
        return false;
    }

    // Check it is executable (if applicable) -
    // kindcheck_type_constructor will not do this.
    if (tc_context->executable) {
        struct UnivarNode node;
        node.must_be_executable = true;
        node.must_be_complete = node.must_be_valid_decreases = false;
        if (!ensure_type_meets_flags(tc_context, &node, *type, &(*type)->location)) {
            return false;
        }
    }

    return true;
}


// ----------------------------------------------------------------------------------------------------

// Type unification.

// Follow the pointers in any non-NULL TY_UNIVAR types.
static struct Type * chase_univars(struct Type *type)
{
    while (type && type->tag == TY_UNIVAR && type->univar_data.node->type != NULL) {
        type = type->univar_data.node->type;
    }
    return type;
}

// Make a new "empty" TY_UNIVAR type. The requirements will be
// must_be_executable if tc_context->executable is true, or no
// requirements otherwise.
static struct Type * new_univar_type(struct TypecheckContext *tc_context)
{
    struct Type *type = make_type(g_no_location, TY_UNIVAR);
    type->univar_data.node = alloc(sizeof(struct UnivarNode));
    type->univar_data.node->must_be_executable = tc_context->executable;
    type->univar_data.node->must_be_complete = false;
    type->univar_data.node->must_be_valid_decreases = false;
    type->univar_data.node->type = NULL;
    type->univar_data.node->ref_count = 1;
    return type;
}

// Ensure type 'type' meets the requirement flags present in 'node'.
// If not, an error is raised. Returns true if successful.
static bool ensure_type_meets_flags(struct TypecheckContext *tc_context,
                                    struct UnivarNode *node,
                                    struct Type *type,
                                    const struct Location *loc)
{
    if (type == NULL) {
        // ignore this error
        return false;
    }

    type = chase_univars(type);

    // must_be_valid_decreases is checked separately
    if (node->must_be_valid_decreases) {
        // Only TY_FINITE_INT, TY_MATH_INT, TY_BOOL, and tuples of
        // those, are currently acceptable for 'decreases'.
        if (type->tag == TY_UNIVAR) {
            type->univar_data.node->must_be_valid_decreases = node->must_be_valid_decreases;
        } else if (type->tag == TY_RECORD) {
            for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
                if (!isdigit((unsigned char)field->name[0])) {
                    // must be a tuple, not a record
                    report_invalid_decreases_type(*loc);
                    tc_context->error = true;
                    return false;
                }
            }
        } else if (type->tag != TY_FINITE_INT && type->tag != TY_MATH_INT && type->tag != TY_BOOL) {
            report_invalid_decreases_type(*loc);
            tc_context->error = true;
            return false;
        }
    }

    // Check must_be_executable and must_be_complete, and check
    // recursively for any "child" types:
    switch (type->tag) {
    case TY_UNIVAR:
        type->univar_data.node->must_be_executable = node->must_be_executable;
        type->univar_data.node->must_be_complete = node->must_be_complete;
        return true;

    case TY_VAR:
    case TY_BOOL:
    case TY_FINITE_INT:
        return true;

    case TY_MATH_INT:
    case TY_MATH_REAL:
        if (node->must_be_executable) {
            report_int_real_not_allowed(*loc);
            tc_context->error = true;
            return false;
        }
        return true;

    case TY_RECORD:
        for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
            if (!ensure_type_meets_flags(tc_context, node, field->type, loc)) {
                return false;
            }
        }
        return true;

    case TY_VARIANT:
        for (struct NameTypeList *variant = type->variant_data.variants; variant; variant = variant->next) {
            if (!ensure_type_meets_flags(tc_context, node, variant->type, loc)) {
                return false;
            }
        }
        return true;

    case TY_ARRAY:
        if (node->must_be_complete) {
            if (!type->array_data.resizable && type->array_data.sizes == NULL) {
                report_incomplete_array_type(*loc);
                tc_context->error = true;
                return false;
            }
        }
        return ensure_type_meets_flags(tc_context, node, type->array_data.element_type, loc);

    case TY_FUNCTION:
        fatal_error("TY_FUNCTION was not expected here");

    case TY_FORALL:
        fatal_error("TY_FORALL was not expected here");

    case TY_LAMBDA:
    case TY_APP:
        fatal_error("This type should have been removed by kind-checking");
    }

    fatal_error("unrecognised type tag");
}

// Unify types by setting LHS := RHS. LHS must be a "NULL" TY_UNIVAR
// type (i.e. a unification variable that hasn't been "resolved" yet).
// LHS must not occur on RHS (this is not checked). Returns true on
// success.
static bool update_univar_type(struct TypecheckContext *tc_context,
                               struct Type *lhs,
                               struct Type *rhs,
                               const struct Location *loc)
{
    if (lhs->tag != TY_UNIVAR || lhs->univar_data.node->type != NULL) {
        fatal_error("update_univar_type: incorrect input");
    }

    if (!ensure_type_meets_flags(tc_context, lhs->univar_data.node, rhs, loc)) {
        return false;
    }

    lhs->univar_data.node->type = copy_type(rhs);
    return true;
}

// Unify two types (or issue an error). This might "fill in" some
// unification variables, but otherwise it will not change either of
// the input types.
// If "exact_match" is false, then it will allow situations where a
// cast would be needed (either numeric or array casts).
// Returns true on success.
static bool unify_types(struct TypecheckContext *tc_context,
                        struct Type *expected_type,
                        struct Type *actual_type,
                        const struct Location *loc,
                        bool exact_match)
{
    // Chase down any already-unified variables in expected_type.
    // Ignore errors if expected_type is NULL.
    expected_type = chase_univars(expected_type);
    if (expected_type == NULL) {
        return false;
    }

    // Same for actual_type.
    actual_type = chase_univars(actual_type);
    if (actual_type == NULL) {
        return false;
    }

    // If expected is TY_UNIVAR (i.e. an unresolved unification variable)
    // then we can just set expected := actual.
    if (expected_type->tag == TY_UNIVAR) {
        if (actual_type->tag == TY_UNIVAR
        && actual_type->univar_data.node == expected_type->univar_data.node) {
            // expected_type and actual_type are the same variable. Do nothing.
            return true;
        } else {
            // Set expected := actual.
            return update_univar_type(tc_context, expected_type, actual_type, loc);
        }
    }

    // If actual is TY_UNIVAR (i.e. an unresolved unification variable)
    // then we can set actual := expected.
    if (actual_type->tag == TY_UNIVAR) {
        return update_univar_type(tc_context, actual_type, expected_type, loc);
    }

    // If we get here, then no unifying is possible, so continue with
    // "normal" type-matching.

    bool ok = true;

    if (expected_type->tag != actual_type->tag) {
        ok = false;

    } else {
        switch (expected_type->tag) {
        case TY_ARRAY:
            // The number of dimensions must match.
            if (expected_type->array_data.ndim != actual_type->array_data.ndim) {
                ok = false;
            }

            // The element types must match exactly (without casting)
            // (but we are allowed to unify if necessary).
            if (ok && !unify_types(tc_context,
                                   expected_type->array_data.element_type,
                                   actual_type->array_data.element_type,
                                   loc,
                                   true)) {
                // unify_types already printed an error message, so just return
                return false;
            }

            // If exact_match is true, then array size and resizability flag must be the same.
            // Otherwise, certain casts are allowed, as outlined below.
            if (exact_match) {
                ok = (expected_type->array_data.resizable == actual_type->array_data.resizable)
                    && (actual_type->array_data.sizes == NULL) == (expected_type->array_data.sizes == NULL);
            } else {
                if (expected_type->array_data.resizable) {
                    // If T[*] is expected then T[*] must be passed.
                    if (!actual_type->array_data.resizable) {
                        ok = false;
                    }

                } else if (expected_type->array_data.sizes == NULL) {
                    // If T[] is expected, then any array (of same ndim and element type)
                    // is acceptable, so nothing to do here.

                } else {
                    // If T[n] is expected, then T[*] and T[] are both acceptable.
                    // T[m] is also acceptable, so long as m == n.
                    if (actual_type->array_data.sizes != NULL
                    && !array_size_terms_equal(expected_type->array_data.sizes,
                                               actual_type->array_data.sizes,
                                               expected_type->array_data.ndim)) {
                        ok = false;
                    }
                }
            }
            break;

        case TY_VAR:
            ok = strcmp(expected_type->var_data.name, actual_type->var_data.name) == 0;
            break;

        case TY_BOOL:
        case TY_MATH_INT:
        case TY_MATH_REAL:
            ok = true;
            break;

        case TY_FINITE_INT:
            // If !exact_match, then FINITE_INT types always match -- a
            // cast will be inserted if necessary.
            // If exact_match, the types have to be equal.
            ok = !exact_match
                || (expected_type->int_data.is_signed == actual_type->int_data.is_signed
                    && expected_type->int_data.num_bits == actual_type->int_data.num_bits);
            break;

        case TY_RECORD:
        case TY_VARIANT:
            {
                struct NameTypeList *exp_list, *act_list;
                if (expected_type->tag == TY_RECORD) {
                    exp_list = expected_type->record_data.fields;
                    act_list = actual_type->record_data.fields;
                } else {
                    exp_list = expected_type->variant_data.variants;
                    act_list = actual_type->variant_data.variants;
                }

                while (ok && exp_list != NULL && act_list != NULL) {
                    // Check for name mismatches.
                    if (exp_list->name == NULL || act_list->name == NULL) {
                        fatal_error("unify_types: field/variant names should not be NULL");
                    }
                    if (strcmp(exp_list->name, act_list->name) != 0) {
                        ok = false;
                    }

                    if (ok) {
                        // Unify the types.
                        // The field/variant types must match exactly.
                        if (!unify_types(tc_context, exp_list->type, act_list->type, loc, true)) {
                            return false;
                        }
                    }

                    // Move on to next list items.
                    exp_list = exp_list->next;
                    act_list = act_list->next;
                }

                if (ok) {
                    // If lists have different lengths, it's an error.
                    if (exp_list != NULL || act_list != NULL) {
                        ok = false;
                    }
                }
            }
            break;

        case TY_FUNCTION:
        case TY_FORALL:
            // This case is not implemented.
            fatal_error("unify_types: expected type cannot be TY_FUNCTION or TY_FORALL");

        case TY_LAMBDA:
        case TY_APP:
            // These should have been removed by kind-checking.
            fatal_error("unify_types called on non-kindchecked type");

        case TY_UNIVAR:
            // Unreachable, as we checked for this case above.
            fatal_error("unreachable code");
        }
    }

    if (!ok) {
        report_type_mismatch_explicit(expected_type, actual_type, *loc);
        tc_context->error = true;
    }
    return ok;
}

// Helper function: Wrap an array term in a cast if needed.
// It is assumed that both types have already been unified (with exact_match==false),
// are non-NULL, and have tag TY_ARRAY.
static void insert_array_cast_if_required(struct Type *expected_type,
                                          struct Type *actual_type,
                                          struct Term **term)
{
    if (expected_type == NULL || actual_type == NULL
    || expected_type->tag != TY_ARRAY || actual_type->tag != TY_ARRAY) {
        fatal_error("this can only be called on array types");
    }

    bool from_resizable = actual_type->array_data.resizable;
    bool from_fixed_size = actual_type->array_data.sizes != NULL;
    bool from_incomplete = !from_resizable && !from_fixed_size;
    bool to_fixed_size = expected_type->array_data.sizes != NULL;
    bool to_incomplete = !to_fixed_size && !expected_type->array_data.resizable;

    if ((from_fixed_size && to_incomplete)
    || (from_incomplete && to_fixed_size)
    || (from_resizable && to_incomplete)
    || (from_resizable && to_fixed_size)) {
        struct Term *new_term = make_term((*term)->location, TM_CAST);
        new_term->type = copy_type(expected_type);
        new_term->cast.target_type = copy_type(expected_type);
        new_term->cast.operand = *term;
        *term = new_term;
    }
}

// Unify term->type with expected_type (both are assumed to be valid types of kind *).
// If allow_casts is true, TM_CAST wrapper(s) may be added.
// If error detected, prints msg and sets tc_context->error.
// Returns true if matching was successful.
static bool match_term_to_type(struct TypecheckContext *tc_context,
                               struct Type *expected_type,
                               struct Term **term)
{
    // First try to unify the types.
    if (!unify_types(tc_context, expected_type, (*term)->type, &(*term)->location, false)) {
        return false;
    }

    // Chase down unification variables.
    expected_type = chase_univars(expected_type);
    struct Type *actual_type = chase_univars((*term)->type);

    // Insert TM_CAST if required.
    if (expected_type && actual_type) {
        if (expected_type->tag == TY_ARRAY) {
            insert_array_cast_if_required(expected_type, actual_type, term);
        } else if (expected_type->tag == TY_FINITE_INT) {
            if (expected_type->int_data.is_signed != actual_type->int_data.is_signed
            || expected_type->int_data.num_bits != actual_type->int_data.num_bits) {
                struct Term *new_term = make_term((*term)->location, TM_CAST);
                new_term->type = copy_type(expected_type);
                new_term->cast.target_type = copy_type(expected_type);
                new_term->cast.operand = *term;
                *term = new_term;
            }
        }
    }

    return true;
}

// This is like match_term_to_type, but specialised for the case where
// the expected_type is TY_BOOL. Returns true if successful.
static bool check_term_is_bool(struct TypecheckContext *tc_context,
                               struct Term *term)
{
    struct Type bool_type;
    bool_type.location = g_no_location;
    bool_type.tag = TY_BOOL;
    return unify_types(tc_context, &bool_type, term->type, &term->location, true);
}

// ----------------------------------------------------------------------------------------------------

// Binary operator typechecking helpers.

enum BinopCategory {
    BINOP_CAT_ANY,
    BINOP_CAT_BOOL_OR_NUMERIC,
    BINOP_CAT_NUMERIC,
    BINOP_CAT_ANY_INTEGER,
    BINOP_CAT_FINITE_INTEGER
};

// This finds the "next bigger" bit-size for a TY_FINITE_INT.
static int bigger_width(int num_bits)
{
    switch (num_bits) {
    case 8: return 16;
    case 16: return 32;
    case 32: return 64;
    case 64: return 128;
    default: fatal_error("bigger_width: no match");
    }
}

// This is used in find_common_binop_type. 'type' is handed over.
// Assumption: type is not TY_UNIVAR.
static struct Type * update_binop_type(struct Term *term, struct Type *type)
{
    struct Type *new_type = chase_univars(term->type);

    // If type is "unset" then it just becomes the type of term (or
    // remains unset).
    if (type == NULL) {
        if (new_type == NULL || new_type->tag == TY_UNIVAR) {
            return NULL;
        } else {
            return copy_type(new_type);
        }
    }

    // Otherwise, see if new_type can be combined with type somehow.

    if (new_type->tag == TY_FINITE_INT && type->tag == TY_FINITE_INT) {
        // For finite-int binops, we will cast all inputs to the
        // smallest type that fit each of the inputs. (This does not
        // necessarily guarantee that the *result* fits into that
        // size, but that will be checked separately by the verifier.)

        // The exception is when you have one i64 input and one u64;
        // then no type can accommodate the full range of both i64 and
        // u64. In that case we use u64 and hope for the best.

        bool need_signed = type->int_data.is_signed || new_type->int_data.is_signed;

        int num_bits = type->int_data.num_bits;
        if (!type->int_data.is_signed && need_signed) {
            num_bits = bigger_width(num_bits);
        }

        int n = new_type->int_data.num_bits;
        if (!new_type->int_data.is_signed && need_signed) {
            n = bigger_width(n);
        }
        if (n > num_bits) {
            num_bits = n;
        }

        if (num_bits == 128) {
            // special case, force u64
            num_bits = 64;
            need_signed = false;
        }

        type->int_data.num_bits = num_bits;
        type->int_data.is_signed = need_signed;

    } else if (new_type->tag == TY_ARRAY && type->tag == TY_ARRAY) {
        // If the size or resizability differs, then cast everything to an
        // incomplete array type.
        if (new_type->array_data.resizable != type->array_data.resizable
        || (new_type->array_data.sizes != NULL) != (type->array_data.sizes != NULL)) {
            type->array_data.resizable = false;
            if (type->array_data.sizes) {
                for (int i = 0; i < type->array_data.ndim; ++i) {
                    free_term(type->array_data.sizes[i]);
                }
                free(type->array_data.sizes);
                type->array_data.sizes = NULL;
            }
        }
    }

    return type;
}

// Find a suitable common type for a binop.
// If this returns a type, that type is the "expected_type", to be unified with
// all terms in the binop. The type must be freed by the caller.
// If this returns NULL, then an error was printed and the caller should give up.
static struct Type * find_common_binop_type(struct TypecheckContext *tc_context,
                                            enum BinopCategory category,
                                            struct TermData_BinOp *binop)
{
    struct Type * type = NULL;
    struct Term * first_term = NULL;

    if (binop->lhs->type == NULL) return NULL; // ignore previous type error
    type = update_binop_type(binop->lhs, type);
    if (type != NULL) first_term = binop->lhs;

    for (struct OpTermList *list = binop->list; list; list = list->next) {
        if (list->rhs->type == NULL) {
            // ignore previous type error
            free_type(type);
            return NULL;
        }
        type = update_binop_type(list->rhs, type);
        if (first_term == NULL && type != NULL) first_term = list->rhs;
    }

    // Check that the selected type is compatible with the binop category.
    bool ok = false;

    switch (category) {
    case BINOP_CAT_ANY:
        ok = true;
        if (type == NULL) type = new_univar_type(tc_context);
        break;

    case BINOP_CAT_BOOL_OR_NUMERIC:
        if (type != NULL && type->tag == TY_BOOL) {
            ok = true;
            break;
        }
        // Fall through

    case BINOP_CAT_NUMERIC:
        if (type != NULL && type->tag == TY_MATH_REAL) {
            ok = true;
            break;
        }
        // Fall through

    case BINOP_CAT_ANY_INTEGER:
        if (type != NULL && type->tag == TY_MATH_INT) {
            ok = true;
            break;
        }
        // Fall through

    case BINOP_CAT_FINITE_INTEGER:
        ok = (type != NULL && type->tag == TY_FINITE_INT);
        break;
    }

    if (!ok) {
        const char *msg = NULL;
        switch (category) {
        case BINOP_CAT_ANY: fatal_error("not possible");
        case BINOP_CAT_BOOL_OR_NUMERIC: msg = "bool or numeric"; break;
        case BINOP_CAT_NUMERIC: msg = "numeric type"; break;
        case BINOP_CAT_ANY_INTEGER: msg = "integer"; break;
        case BINOP_CAT_FINITE_INTEGER: msg = "finite-sized integer"; break;
        }
        report_type_mismatch_string(msg, first_term);
        tc_context->error = true;
        free_type(type);
        return NULL;
    }

    return type;
}

// Checks that binop args are valid.
// If TY_FINITE_INT, cast all args to the same bitsize and signedness.
// If TY_ARRAY (and BINOP_CAT_ANY), cast the arrays to T[] if required.
static bool check_binop_args(struct TypecheckContext *tc_context,
                             struct Term *binop,
                             enum BinopCategory cat)
{
    struct TermData_BinOp *data = &binop->binop;

    // Find a suitable common type.
    struct Type *type = find_common_binop_type(tc_context, cat, data);
    if (!type) {
        return false;
    }

    // Now match each operand to the common type.
    if (!match_term_to_type(tc_context, type, &data->lhs)) {
        free_type(type);
        return false;
    }
    for (struct OpTermList *list = data->list; list; list = list->next) {
        if (!match_term_to_type(tc_context, type, &list->rhs)) {
            free_type(type);
            return false;
        }
    }

    free_type(type);
    return true;
}


// ----------------------------------------------------------------------------------------------------

//
// Term typechecking
//

static void free_type_value(void *context, const char *key, void *value)
{
    free_type(value);
}

// Add implied type-arguments to a term of type TY_FORALL.
static void infer_type_arguments(struct TypecheckContext *tc_context,
                                 struct Term *term)
{
    if (term->type->tag != TY_FORALL) {
        fatal_error("improper call to infer_type_arguments");
    }

    // Create a substitution mapping each type-variable-name to a new
    // TY_UNIVAR type. Also create a list of all the new TY_UNIVARs.
    struct TypeList *tyargs = NULL;
    struct TypeList **tail = &tyargs;
    struct HashTable *theta = new_hash_table();
    for (struct TyVarList *tyvar = term->type->forall_data.tyvars; tyvar; tyvar = tyvar->next) {
        struct Type *ty = new_univar_type(tc_context);
        *tail = alloc(sizeof(struct TypeList));
        (*tail)->type = copy_type(ty);
        (*tail)->next = NULL;
        tail = &(*tail)->next;
        hash_table_insert(theta, tyvar->name, ty);
    }

    // Calculate a new type (stripping out the TY_FORALL, effectively).
    struct Type *new_type = substitute_in_type_from_hashtable(theta, term->type->forall_data.type);

    // Change the term itself, by wrapping it in TM_TYAPP.
    struct Term *old_term = alloc(sizeof(struct Term));
    *old_term = *term;
    term->tag = TM_TYAPP;
    term->type = new_type;
    term->tyapp.lhs = old_term;
    term->tyapp.tyargs = tyargs;

    // Finally, free our hash table.
    hash_table_for_each(theta, free_type_value, NULL);
    free_hash_table(theta);
}

// If the input term has type TY_VARIANT and has one of the following forms:
//  - TM_VAR referring to a data constructor
//  - TM_TYAPP wrapping a data constructor TM_VAR
//  - TM_CALL where the function is one of the above two options.
// then reduce it directly to a TM_VARIANT with appropriate payload.
// Otherwise, leave the term unchanged.
static void reduce_constructor(struct TypecheckContext *tc_context,
                               struct Term *term)
{
    if (term->type == NULL || chase_univars(term->type)->tag != TY_VARIANT) {
        return;
    }

    // Inspect the term, see if we are in one of the above cases.
    struct Term *base_term = term;
    if (base_term->tag == TM_CALL) {
        base_term = base_term->call.func;
    }
    if (base_term->tag == TM_TYAPP) {
        base_term = base_term->tyapp.lhs;
    }
    if (base_term->tag != TM_VAR) {
        return;
    }

    // See if the variable corresponds to a data constructor.
    struct TypeEnvEntry * entry = lookup_type_info(tc_context, base_term->var.name);
    if (entry == NULL) {
        fatal_error("could not find variable information");
    }
    if (!entry->constructor) {
        return;
    }

    // Extract the data we need for the new term.
    const char * variant_name = base_term->var.name;
    base_term->var.name = NULL;

    struct Term *payload = NULL;
    if (term->tag == TM_VAR || term->tag == TM_TYAPP) {
        // The payload is {} in these cases.
        payload = make_term(term->location, TM_RECORD);
        payload->record.fields = NULL;
        payload->type = make_type(g_no_location, TY_RECORD);
        payload->type->record_data.fields = NULL;
    } else {
        // The payload is the argument to the call - there should be just one
        if (term->tag != TM_CALL || term->call.args->next != NULL) {
            fatal_error("data constructor application: term not of expected form");
        }
        payload = term->call.args->rhs;
        term->call.args->rhs = NULL;
    }

    // Strip down the term
    if (term->tag == TM_TYAPP) {
        free_term(term->tyapp.lhs);
        free_type_list(term->tyapp.tyargs);
    } else if (term->tag == TM_CALL) {
        free_term(term->call.func);
        free_op_term_list(term->call.args);
    }

    // Reconstruct it as a TM_VARIANT. (The type and location are left unchanged.)
    term->tag = TM_VARIANT;
    term->variant.variant_name = variant_name;
    term->variant.payload = payload;
}

// Typecheck a TM_VAR term.
//   func_call_lhs = true if the term appears as the "lhs" of a TM_CALL, e.g. f(100).
//   tyapp_lhs = true if the term appears as the "lhs" of a TM_TYAPP, e.g. f<i32>.
//   If both are true, the term is the lhs of a TM_TYAPP which is itself the lhs of
//     a TM_CALL, e.g. f<i32>(100).
static void typecheck_var_term(struct TypecheckContext *tc_context,
                               struct Term *term,
                               bool func_call_lhs,
                               bool tyapp_lhs)
{
    if (term->tag != TM_VAR) {
        fatal_error("typecheck_var_term: must be called on TM_VAR");
    }

    // Look up the TypeEnvEntry for this variable name
    struct TypeEnvEntry * entry = lookup_type_info(tc_context, term->var.name);

    if (entry == NULL) {
        // This happens when there was an error with the original declaration
        // of the variable, so the variable never got inserted into the env.
        // Ignore any further errors relating to this variable.
        tc_context->error = true;
        return;
    }

    if (entry->type == NULL) {
        fatal_error("missing type for variable, this is unexpected");
    }

    // Ghost variables can only be accessed from *nonexecutable* contexts.
    if (entry->ghost && tc_context->executable) {
        report_access_ghost_var_from_executable_code(term);
        tc_context->error = true;
        return;
    }

    // Impure functions can only be accessed from impure, executable functions.
    if (entry->impure && !tc_context->executable) {
        report_access_impure_fun_from_ghost_code(term);
        tc_context->error = true;
        return;
    }
    if (entry->impure && !tc_context->impure) {
        report_access_impure_fun_from_pure_code(term);
        tc_context->error = true;
        return;
    }

    // Set the type.
    term->type = copy_type(chase_univars(entry->type));

    // Add inferred type-arguments if necessary.
    if (term->type->tag == TY_FORALL && !tyapp_lhs) {
        infer_type_arguments(tc_context, term);
    }

    // If we are left with TY_FUNCTION then this is only allowed as a func_call_lhs.
    if (term->type->tag == TY_FUNCTION && !func_call_lhs) {
        report_function_variable_not_allowed(term->location);
        tc_context->error = true;
        free_type(term->type);
        term->type = NULL;
    }

    // Change constructor TM_VARs into TM_VARIANTs, if applicable.
    reduce_constructor(tc_context, term);
}

static void typecheck_tyapp_term(struct TypecheckContext *tc_context,
                                 struct Term *term,
                                 bool func_call_lhs)
{
    if (term->tag != TM_TYAPP) {
        fatal_error("typecheck_tyapp_term: must be called on TM_TYAPP");
    }

    // Typecheck the LHS
    if (term->tyapp.lhs->tag == TM_VAR) {
        typecheck_var_term(tc_context, term->tyapp.lhs, func_call_lhs, true);
    } else {
        typecheck_term(tc_context, term->tyapp.lhs);
    }
    if (term->tyapp.lhs->type == NULL) {
        return;
    }

    // Kind-check all type arguments and count them
    int num_tyargs_present = 0;
    for (struct TypeList *tyarg = term->tyapp.tyargs; tyarg; tyarg = tyarg->next) {
        if (!kindcheck_type(tc_context, &tyarg->type)) {
            return;
        }
        ++num_tyargs_present;
    }

    // LHS must be TY_FORALL.
    if (term->tyapp.lhs->type->tag != TY_FORALL) {
        report_type_arguments_not_expected_here(term->location);
        tc_context->error = true;
        return;
    }

    // The number of type arguments given should correspond to the
    // number expected by the TY_FORALL.
    int num_tyargs_expected = tyvar_list_length(term->tyapp.lhs->type->forall_data.tyvars);
    if (num_tyargs_expected != num_tyargs_present) {
        report_wrong_number_of_type_arguments(term->location, num_tyargs_expected, num_tyargs_present);
        tc_context->error = true;
        return;
    }

    // LHS should be TM_VAR - because this is the only thing that can
    // have a TY_FORALL type (currently).
    if (term->tyapp.lhs->tag != TM_VAR) {
        fatal_error("unexpected: non-variable term of type TY_FORALL");
    }

    // The final type is constructed by substituting the type
    // arguments into the forall-type.
    term->type = substitute_in_type_from_list(term->tyapp.lhs->type->forall_data.tyvars,
                                              term->tyapp.tyargs,
                                              term->tyapp.lhs->type->forall_data.type);

    // If we end up with TY_FUNCTION type, then it must be in func call position.
    if (term->type->tag == TY_FUNCTION && !func_call_lhs) {
        report_function_variable_not_allowed(term->location);
        free_type(term->type);
        term->type = NULL;
        return;
    }

    // Change constructor tyapps (e.g. Nothing<i32>) into TM_VARIANTs, if applicable.
    reduce_constructor(tc_context, term);
}

static void* typecheck_var(void *context, struct Term *term, void *type_result)
{
    typecheck_var_term(context, term, false, false);
    return NULL;
}

static void* typecheck_bool_literal(void *context, struct Term *term, void *type_result)
{
    // Bool literals are always of type bool
    term->type = make_type(g_no_location, TY_BOOL);
    return NULL;
}

static bool string_to_int(const char *p,
                          uint64_t *abs_value_out,
                          bool *negative_out)
{
    uint64_t abs_value = 0;
    bool negative = false;

    if (*p == '-') {
        p++;
        negative = true;
    }

    while (*p) {
        uint64_t digit = (*p++ - '0');

        if (abs_value >= UINT64_C(1844674407370955162) || (abs_value == UINT64_C(1844674407370955161) && digit >= 6)) {
            // this case is where the absolute value of the number is larger than UINT64_MAX
            return false;
        }

        abs_value = abs_value * 10 + digit;
    }

    *abs_value_out = abs_value;
    *negative_out = negative;
    return true;
}

static bool int_value_in_range(int num_bits, bool is_signed, uint64_t abs_value, bool negative)
{
    switch (num_bits) {
    case 8:
        if (is_signed) {
            return abs_value <= 127
                || (negative && abs_value == 128);
        } else {
            return !negative && abs_value <= 255;
        }

    case 16:
        if (is_signed) {
            return abs_value <= 32767
                || (negative && abs_value == 32768);
        } else {
            return !negative && abs_value <= 65535;
        }

    case 32:
        if (is_signed) {
            return abs_value <= UINT64_C(2147483647)
                || (negative && abs_value == UINT64_C(2147483648));
        } else {
            return !negative && abs_value <= UINT64_C(4294967295);
        }

    case 64:
        if (is_signed) {
            return abs_value <= UINT64_C(9223372036854775807) || (negative && abs_value == UINT64_C(9223372036854775808));
        } else {
            return !negative;
        }
    }

    fatal_error("invalid num_bits for integer");
}

static void* typecheck_int_literal(void *context, struct Term *term, void *type_result)
{
    struct TypecheckContext* tc_context = context;

    // Int literals are typed as i32, u32, i64 or u64 (in that order of preference).
    // Typechecking can fail, if the literal is outside the i64 or u64 range.

    // Read the absolute value of the number into a uint64_t, and read the sign bit
    uint64_t abs_value;
    bool negative;
    bool valid = string_to_int(term->int_literal.data, &abs_value, &negative);

    // Fill in the type based on the size of the literal
    if (valid) {
        if (int_value_in_range(32, true, abs_value, negative)) {
            term->type = make_int_type(g_no_location, true, 32);

        } else if (int_value_in_range(32, false, abs_value, negative)) {
            term->type = make_int_type(g_no_location, false, 32);

        } else if (int_value_in_range(64, true, abs_value, negative)) {
            term->type = make_int_type(g_no_location, true, 64);
        
        } else if (int_value_in_range(64, false, abs_value, negative)) {
            term->type = make_int_type(g_no_location, false, 64);
        
        } else {
            // this case is where the absolute value of the number fits into a uint64_t, but the sign is negative and
            // the number is outside the int64_t range
            valid = false;
        }
    }

    if (!valid) {
        report_int_literal_too_big(term->location);
        tc_context->error = true;
    }

    return NULL;
}

static void* typecheck_string_literal(void *context, struct Term *term, void *type_result)
{
    // String literals currently have type u8[N], where N is the
    // (compile time known) size of the string.

    char buf[50];
    sprintf(buf, "%" PRIu32, term->string_literal.length);

    term->type = make_type(g_no_location, TY_ARRAY);
    term->type->array_data.element_type = make_int_type(g_no_location, false, 8);
    term->type->array_data.ndim = 1;
    term->type->array_data.resizable = false;
    term->type->array_data.sizes = alloc(sizeof(struct Term *));
    term->type->array_data.sizes[0] = make_int_literal_term(g_no_location, buf);

    return NULL;
}

static void* typecheck_array_literal(void *context, struct Term *term, void *type_result, void *list_result)
{
    struct TypecheckContext *tc_context = context;

    struct Type *elem_type = new_univar_type(tc_context);
    uint64_t num_elements = 0;

    for (struct OpTermList *node = term->array_literal.terms; node; node = node->next) {
        if (node->rhs->type == NULL || !match_term_to_type(tc_context, elem_type, &node->rhs)) {
            free_type(elem_type);
            return NULL;
        }
        ++num_elements;
    }

    char buf[50];
    sprintf(buf, "%" PRIu64, num_elements);

    term->type = make_type(g_no_location, TY_ARRAY);
    term->type->array_data.element_type = elem_type;
    term->type->array_data.ndim = 1;
    term->type->array_data.resizable = false;
    term->type->array_data.sizes = alloc(sizeof(struct Term *));
    term->type->array_data.sizes[0] = make_int_literal_term(g_no_location, buf);

    return NULL;
}

static bool valid_cast_type(enum TypeTag tag)
{
    return tag == TY_FINITE_INT
        || tag == TY_MATH_INT
        || tag == TY_MATH_REAL;
}

static void* typecheck_cast(void *context, struct Term *term, void *type_result, void *target_type_result, void *operand_result)
{
    struct TypecheckContext *tc_context = context;

    if (term->cast.operand->type == NULL) {
        return NULL;
    }

    // all user-supplied types must be kindchecked!
    if (!kindcheck_type(context, &term->cast.target_type)) {
        return NULL;
    }

    // Casting is allowed from/to TY_FINITE_INT, TY_MATH_INT and TY_MATH_REAL.

    // (Note: TM_CAST also supports casting to/from array types, but
    // currently, such TM_CAST terms are inserted by the typechecker
    // only -- i.e. we should not see an array TM_CAST in the input.)

    // (Also: we don't currently handle the case where the operand type
    // is an unresolved TY_UNIVAR, because we don't currently have the
    // machinery to be able to constrain a TY_UNIVAR to a numeric type.)

    enum TypeTag from_type = chase_univars(term->cast.operand->type)->tag;
    enum TypeTag to_type = term->cast.target_type->tag;

    if (!valid_cast_type(from_type) || !valid_cast_type(to_type)) {
        report_invalid_cast(term);
        tc_context->error = true;
    } else {
        term->type = copy_type(term->cast.target_type);
    }

    return NULL;
}

static void* typecheck_if(void *context, struct Term *term, void *type_result, void *cond_result, void *then_result, void *else_result)
{
    struct TypecheckContext *tc_context = context;

    bool cond_ok = check_term_is_bool(tc_context,
                                      term->if_data.cond);

    bool branches_ok =
        match_term_to_type(tc_context,
                           term->if_data.then_branch->type,
                           &term->if_data.else_branch);

    if (cond_ok && branches_ok) {
        term->type = copy_type(term->if_data.then_branch->type);
    }

    return NULL;
}

static void* typecheck_unop(void *context, struct Term *term, void *type_result, void *operand_result)
{
    struct TypecheckContext *tc_context = context;

    struct Term *operand = term->unop.operand;
    enum UnOp operator = term->unop.operator;

    if (operand->type == NULL) {
        return NULL;
    }

    bool ok = true;

    struct Type *type = chase_univars(operand->type);

    bool numeric = type->tag == TY_FINITE_INT
        || type->tag == TY_MATH_INT
        || type->tag == TY_MATH_REAL;

    bool is_signed = type->tag != TY_FINITE_INT || type->int_data.is_signed;

    switch (operator) {
    case UNOP_NEGATE:
        if (!numeric || !is_signed) {
            report_type_mismatch_string("signed numeric type", operand);
            tc_context->error = true;
            ok = false;
        }
        break;

    case UNOP_COMPLEMENT:
        if (type->tag != TY_FINITE_INT) {
            report_type_mismatch_string("finite-sized integer", operand);
            tc_context->error = true;
            ok = false;
        }
        break;

    case UNOP_NOT:
        ok = check_term_is_bool(tc_context, operand);
        break;
    }

    if (ok) {
        term->type = copy_type(type);
    }

    return NULL;
}

enum Direction {
    DIR_NEUTRAL,
    DIR_POINTS_LEFT,
    DIR_POINTS_RIGHT
};

enum Direction operator_direction(enum BinOp op)
{
    switch (op) {
    case BINOP_LESS:
    case BINOP_LESS_EQUAL:
    case BINOP_IMPLIED_BY:
        return DIR_POINTS_LEFT;

    case BINOP_GREATER:
    case BINOP_GREATER_EQUAL:
    case BINOP_IMPLIES:
        return DIR_POINTS_RIGHT;

    case BINOP_EQUAL:
    case BINOP_NOT_EQUAL:
        return DIR_NEUTRAL;

    default:
        fatal_error("operator shouldn't be part of a chain");
    }
}

static bool check_chain_direction(struct TypecheckContext *tc_context, struct Term *term)
{
    enum Direction dir = DIR_NEUTRAL;
    if (term->tag != TM_BINOP) return true;
    if (term->binop.list->next == NULL) return true;  // not a chain

    for (struct OpTermList *node = term->binop.list; node; node = node->next) {
        enum Direction new_dir = operator_direction(node->operator);
        if ((new_dir == DIR_POINTS_LEFT && dir == DIR_POINTS_RIGHT) ||
        (new_dir == DIR_POINTS_RIGHT && dir == DIR_POINTS_LEFT)) {
            if (node->operator == BINOP_IMPLIES || node->operator == BINOP_IMPLIED_BY) {
                report_implies_direction_error(node->rhs->location);
            } else {
                report_chaining_direction_error(node->rhs->location);
            }
            tc_context->error = true;
            return false;
        } else if (new_dir != DIR_NEUTRAL) {
            dir = new_dir;
        }
    }

    return true;
}

static void break_chain(struct TypecheckContext *tc_context, struct Term *term)
{
    if (term->binop.list->next == NULL) {
        return;
    }

    // term is: a < b < ...

    if (term->binop.list->rhs->tag == TM_VAR) {

        // Optimisation for a common case where b is a variable (e.g.
        // "1 <= x <= 10").

        // Create:
        // tm1:  a < b
        // tm2:  b < ...    (Recursively break chain in this term)
        // result: tm1 && tm2

        struct Term * term_a = term->binop.lhs;
        enum BinOp operator = term->binop.list->operator;
        struct Term * term_b = term->binop.list->rhs;
        struct OpTermList * tail_list = term->binop.list->next;
        free(term->binop.list);

        struct Term * tm1 = make_term(term->location, TM_BINOP);
        tm1->type = copy_type(term->type);
        tm1->binop.lhs = term_a;
        tm1->binop.list = alloc(sizeof(struct OpTermList));
        tm1->binop.list->operator = operator;
        tm1->binop.list->rhs = copy_term(term_b);
        tm1->binop.list->next = NULL;

        struct Term * tm2 = make_term(term_b->location, TM_BINOP);
        tm2->type = copy_type(term->type);
        tm2->location.end_line_num = term->location.end_line_num;
        tm2->location.end_column_num = term->location.end_column_num;
        tm2->binop.lhs = term_b;
        tm2->binop.list = tail_list;

        break_chain(tc_context, tm2);

        term->binop.lhs = tm1;
        term->binop.list = alloc(sizeof(struct OpTermList));
        term->binop.list->operator = BINOP_AND;
        term->binop.list->rhs = tm2;
        term->binop.list->next = NULL;

    } else {

        // General case where we don't want to duplicate "b", so
        // introduce a let instead.

        // Create:
        //  tm1:  a < fresh_name
        //  tm2:  fresh_name < ...    (Recursively break chain in tm2)
        //  result: let fresh_name = b in tm1 && tm2

        char buf[40];
        sprintf(buf, "%" PRIu64, tc_context->temp_name_counter++);
        char * fresh_name = copy_string_2("chain@@", buf);

        struct Term * term_a = term->binop.lhs;
        enum BinOp operator = term->binop.list->operator;
        struct Term * term_b = term->binop.list->rhs;
        struct OpTermList * tail_list = term->binop.list->next;
        free(term->binop.list);

        struct Term * tm1 = make_term(term->location, TM_BINOP);
        tm1->type = copy_type(term->type);
        tm1->binop.lhs = term_a;
        tm1->binop.list = alloc(sizeof(struct OpTermList));
        tm1->binop.list->operator = operator;
        tm1->binop.list->rhs = make_var_term(term->location, fresh_name);
        tm1->binop.list->rhs->type = copy_type(term_b->type);
        tm1->binop.list->next = NULL;

        struct Term * tm2 = make_term(term_b->location, TM_BINOP);
        tm2->type = copy_type(term->type);
        tm2->location.end_line_num = term->location.end_line_num;
        tm2->location.end_column_num = term->location.end_column_num;
        tm2->binop.lhs = make_var_term(term->location, fresh_name);
        tm2->binop.lhs->type = copy_type(term_b->type);
        tm2->binop.list = tail_list;

        break_chain(tc_context, tm2);

        struct Term * and_term = make_term(term->location, TM_BINOP);
        and_term->type = copy_type(term->type);
        and_term->binop.lhs = tm1;
        and_term->binop.list = alloc(sizeof(struct OpTermList));
        and_term->binop.list->operator = BINOP_AND;
        and_term->binop.list->rhs = tm2;
        and_term->binop.list->next = NULL;

        term->tag = TM_LET;
        term->let.name = fresh_name;
        term->let.rhs = term_b;
        term->let.body = and_term;
    }
}

static struct Location get_location_from_op_term_list(struct OpTermList *list)
{
    struct Location loc = list->rhs->location;

    // move to final (non-NULL) node in the list
    while (list->next) {
        list = list->next;
    }

    set_location_end(&loc, &list->rhs->location);

    return loc;
}

static void reverse_implication_list(struct OpTermList **list)
{
    struct OpTermList *node = *list;
    struct OpTermList *next = NULL;

    while (node) {
        node->operator = BINOP_IMPLIES;

        // swap node->next and next
        struct OpTermList *tmp = node->next;
        node->next = next;
        next = tmp;

        // swap node and next
        tmp = next;
        next = node;
        node = tmp;
    }

    // The reversed list ends up in 'next'
    *list = next;
}

static void break_implies_chain(struct Term *term)
{
    if (term->binop.list->operator == BINOP_IMPLIES) {
        // We want to turn A ==> B ==> C ==> D into A ==> (B ==> (C ==> D)).

        // Let term be:
        //   lhs = A
        //   list = (==>, B, (==>, C, Tail))

        // Let new_term be:
        //   lhs = B
        //   list = (==>, C, Tail)

        // Rewrite term to:
        //   lhs = A
        //   list = (==>, break_implies_chain(new_term), NULL)

        if (term->binop.list->next != NULL) {
            struct Location new_loc = get_location_from_op_term_list(term->binop.list);
            struct Term *new_term = make_term(new_loc, TM_BINOP);
            new_term->type = copy_type(term->type);  // this will be TY_BOOL

            new_term->binop.lhs = term->binop.list->rhs;
            new_term->binop.list = term->binop.list->next;

            break_implies_chain(new_term);

            term->binop.list->rhs = new_term;
            term->binop.list->next = NULL;
        }

    } else if (term->binop.list->operator == BINOP_IMPLIED_BY) {
        // We want to turn A <== B <== C <== D into D ==> (C ==> (B ==> A)).

        // We do this in two steps: first "reverse" the term, turning it into
        // into D ==> C ==> B ==> A; then call break_implies_chain recursively
        // to turn that into D ==> (C ==> (B ==> A)).

        struct OpTermList *temp_list = alloc(sizeof(struct OpTermList));
        temp_list->rhs = term->binop.lhs;
        temp_list->next = term->binop.list;

        reverse_implication_list(&temp_list);

        term->binop.lhs = temp_list->rhs;
        term->binop.list = temp_list->next;

        free(temp_list);

        break_implies_chain(term);
    }
}

static void* typecheck_binop(void *context, struct Term *term, void *type_result, void *result1, void *result2)
{
    struct TypecheckContext *tc_context = context;

    enum BinOp op = term->binop.list->operator;

    switch (op) {
    case BINOP_PLUS:
    case BINOP_MINUS:
    case BINOP_TIMES:
    case BINOP_DIVIDE:
    case BINOP_MODULO:
    case BINOP_BITAND:
    case BINOP_BITOR:
    case BINOP_BITXOR:
    case BINOP_LESS:
    case BINOP_LESS_EQUAL:
    case BINOP_GREATER:
    case BINOP_GREATER_EQUAL:
    case BINOP_EQUAL:
    case BINOP_NOT_EQUAL:
        {
            // == and != can work on bools or numeric types.
            // Modulo requires integers.
            // BIT operators require finite integers.
            // All others require any numeric type.
            // (exception: in ghost code, == and != can be used at any non-function type)

            enum BinopCategory cat;
            if (op == BINOP_EQUAL || op == BINOP_NOT_EQUAL) {
                if (tc_context->executable) {
                    cat = BINOP_CAT_BOOL_OR_NUMERIC;
                } else {
                    cat = BINOP_CAT_ANY;
                }
            } else if (op == BINOP_MODULO) {
                cat = BINOP_CAT_ANY_INTEGER;
            } else if (op == BINOP_BITAND || op == BINOP_BITOR || op == BINOP_BITXOR) {
                cat = BINOP_CAT_FINITE_INTEGER;
            } else {
                cat = BINOP_CAT_NUMERIC;
            }

            if (check_binop_args(tc_context, term, cat)) {

                // The comparisons return bool, others return the same type as their argument.
                if (op == BINOP_LESS || op == BINOP_LESS_EQUAL
                || op == BINOP_GREATER || op == BINOP_GREATER_EQUAL
                || op == BINOP_EQUAL || op == BINOP_NOT_EQUAL) {
                    term->type = make_type(g_no_location, TY_BOOL);
                } else {
                    term->type = copy_type(term->binop.lhs->type);
                }

                check_chain_direction(tc_context, term);
                break_chain(tc_context, term);
            }
        }
        break;

    case BINOP_SHIFTLEFT:
    case BINOP_SHIFTRIGHT:
        {
            // Two integers required, but they don't necessarily have to have same size/signedness.
            // Result has same type as lhs.
            // (Note: the parser will not chain shift operators, so only two operands to worry about.)

            // Note: TY_MATH_INT not supported for shifts currently.

            bool ok = true;

            if (chase_univars(term->binop.lhs->type)->tag != TY_FINITE_INT) {
                report_type_mismatch_string("finite-sized integer", term->binop.lhs);
                tc_context->error = true;
                ok = false;
            }

            if (chase_univars(term->binop.list->rhs->type)->tag != TY_FINITE_INT) {
                report_type_mismatch_string("finite-sized integer", term->binop.list->rhs);
                tc_context->error = true;
                ok = false;
            }

            if (ok) {
                term->type = copy_type(term->binop.lhs->type);
            }
        }
        break;

    case BINOP_AND:
    case BINOP_OR:
    case BINOP_IMPLIES:
    case BINOP_IMPLIED_BY:
    case BINOP_IFF:
        {
            // all operands must be bool
            bool ok = check_term_is_bool(tc_context, term->binop.lhs);
            for (struct OpTermList *node = term->binop.list; node; node = node->next) {
                ok = check_term_is_bool(tc_context, node->rhs) && ok;
            }

            if (ok) {
                term->type = make_type(g_no_location, TY_BOOL);
                check_chain_direction(tc_context, term);
                break_implies_chain(term);
            }
        }
        break;
    }

    return NULL;
}

static bool is_lvalue(const struct TypecheckContext *tc_context, struct Term *term,
                      bool *ghost_out, bool *readonly_out)
{
    if (term->tag == TM_FIELD_PROJ) {
        // X.field is an lvalue if and only if X is.
        return is_lvalue(tc_context, term->field_proj.lhs, ghost_out, readonly_out);
    }

    if (term->tag == TM_ARRAY_PROJ) {
        // X[i,j] is an lvalue if and only if X is.
        return is_lvalue(tc_context, term->array_proj.lhs, ghost_out, readonly_out);
    }

    if (term->tag == TM_STRING_LITERAL) {
        // a string literal is a non-modifiable lvalue
        if (ghost_out) *ghost_out = false;
        if (readonly_out) *readonly_out = true;
        return true;
    }

    if (term->tag == TM_CAST && term->type && chase_univars(term->type)->tag == TY_ARRAY) {
        // Array casts inherit their "lvalueness" from the underlying operand.
        // (Numeric casts are never lvalues.)
        return is_lvalue(tc_context, term->cast.operand, ghost_out, readonly_out);
    }

    if (term->tag != TM_VAR) {
        return false;
    }

    struct TypeEnvEntry *entry = lookup_type_info(tc_context, term->var.name);

    if (entry == NULL) {
        // this happens when a variable was 'poisoned' due to a previous error.
        // let's pretend it's an lvalue, this will help avoid further errors.
        if (ghost_out) *ghost_out = false;
        if (readonly_out) *readonly_out = false;
        return true;
    }

    if (entry->constructor) {
        // a constructor isn't considered an lvalue
        return false;
    }

    if (ghost_out) *ghost_out = entry->ghost;
    if (readonly_out) *readonly_out = entry->read_only;
    return true;
}

static void* nr_typecheck_let(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct TypecheckContext *tc_context = context;

    transform_term(tr, context, term->let.rhs);
    if (!term->let.rhs->type) {
        return NULL;
    }

    add_to_type_env(tc_context->type_env,
                    term->let.name,
                    copy_type(term->let.rhs->type),   // handover
                    !tc_context->executable,   // ghost
                    true,                      // read-only
                    false,                     // constructor
                    false);                    // impure

    transform_term(tr, context, term->let.body);

    term->type = copy_type(term->let.body->type);

    return NULL;
}

static void* nr_typecheck_quantifier(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct TypecheckContext *tc_context = context;

    if (tc_context->executable) {
        report_executable_quantifier(term);
        tc_context->error = true;
        return NULL;
    }

    // user-supplied type annotation, requires kindchecking
    if (!kindcheck_type(tc_context, &term->quant.type)) {
        return NULL;
    }

    add_to_type_env(tc_context->type_env,
                    term->quant.name,
                    copy_type(term->quant.type),     // handover
                    true,    // ghost
                    true,    // read-only
                    false,   // constructor
                    false);  // impure

    transform_term(tr, context, term->quant.body);

    // Quantifier body must be boolean
    bool ok = check_term_is_bool(tc_context, term->quant.body);

    // Quantifier has type boolean
    if (ok) {
        term->type = make_type(g_no_location, TY_BOOL);
    }

    return NULL;
}

static void* nr_typecheck_call(struct TermTransform *tr, void *context,
                               struct Term *term, void *type_result)
{
    struct TypecheckContext *tc_context = context;

    // Typecheck the arguments.
    transform_op_term_list(tr, context, term->call.args);

    // Typecheck the LHS.
    if (term->call.func->tag == TM_VAR) {
        typecheck_var_term(tc_context, term->call.func, true, false);
    } else if (term->call.func->tag == TM_TYAPP) {
        typecheck_tyapp_term(tc_context, term->call.func, true);
    } else {
        // This is probably a type error, but we'll typecheck the 'func' term anyway
        typecheck_term(tc_context, term->call.func);
    }

    struct Type * fun_type = chase_univars(term->call.func->type);
    if (fun_type == NULL) {
        // LHS term didn't typecheck. (Don't print further errors.)
        return NULL;
    }
    if (fun_type->tag != TY_FUNCTION) {
        // LHS term isn't a function; we can't call it.
        report_call_of_non_function(term->call.func);
        tc_context->error = true;
        return NULL;
    }

    bool ok = true;

    // Check whether we are allowed to pass ref arguments.
    struct Statement *stmt = tc_context->statement;
    bool allow_ref = false;
    bool ignoring_ret_val = false;
    if (stmt) {
        if (stmt->tag == ST_CALL) {
            allow_ref = ignoring_ret_val = (stmt->call.term == term);
        } else if (stmt->tag == ST_ASSIGN) {
            allow_ref = (stmt->assign.rhs == term);
        } else if (stmt->tag == ST_VAR_DECL) {
            allow_ref = (stmt->var_decl.rhs == term);
        }
    }

    // Check that the correct number of term arguments have been supplied
    struct FunArg *dummy_list = fun_type->function_data.args;
    struct OpTermList *actual_list = term->call.args;
    while (dummy_list && actual_list) {
        dummy_list = dummy_list->next;
        actual_list = actual_list->next;
    }
    if (dummy_list || actual_list) {
        report_wrong_number_of_arguments(term);
        tc_context->error = true;
        ok = false;

    } else {
        // Check that the actual arguments match the function's formal parameter types
        dummy_list = fun_type->function_data.args;
        actual_list = term->call.args;

        while (dummy_list && actual_list) {
            if (!match_term_to_type(tc_context, dummy_list->type, &actual_list->rhs)) {
                ok = false;
            }

            // For typechecking purposes, 'ref' arguments must be
            // writable lvalues (and allow_ref must be true).
            if (dummy_list->ref) {

                bool ghost = false;
                bool read_only = false;
                bool lvalue = is_lvalue(tc_context, actual_list->rhs, &ghost, &read_only);

                if (!allow_ref) {
                    report_ref_arg_not_allowed(actual_list->rhs->location);
                    tc_context->error = true;
                    ok = false;
                } else if (!lvalue) {
                    report_cannot_take_ref(actual_list->rhs->location);
                    tc_context->error = true;
                    ok = false;
                } else if (read_only) {
                    report_cannot_take_ref_to_readonly(actual_list->rhs->location);
                    tc_context->error = true;
                    ok = false;
                } else if (!ghost && !tc_context->executable) {
                    // Trying to write to a non-ghost variable in a ghost context.
                    report_writing_nonghost_from_ghost_code(term->location);
                    tc_context->error = true;
                    ok = false;
                }
            }

            dummy_list = dummy_list->next;
            actual_list = actual_list->next;
        }

        // Check whether we expect to have a return value or not.
        if (ignoring_ret_val) {
            if (fun_type->function_data.return_type != NULL) {
                report_function_return_value_ignored(term->call.func);
                tc_context->error = true;
                ok = false;
            }
        } else {
            if (fun_type->function_data.return_type == NULL) {
                report_function_does_not_return_a_value(term->call.func);
                tc_context->error = true;
                ok = false;
            }
        }
    }

    if (ok) {
        term->type = copy_type(fun_type->function_data.return_type);

        // Reduce constructor TM_CALLs to TM_VARIANTs, if applicable.
        reduce_constructor(tc_context, term);
    }

    return NULL;
}

static void * nr_typecheck_tyapp(struct TermTransform *tr, void *context,
                                 struct Term *term, void *type_result)
{
    typecheck_tyapp_term(context, term, false);
    return NULL;
}

static void* typecheck_record(void *context, struct Term *term, void *type_result, void *fields_result)
{
    // Tuple or record term

    struct TypecheckContext *tc_context = context;

    // first pass: number the positional fields,
    // and check for mixed positional and named fields
    int field_num = 0;
    bool found_number = false;
    bool found_name = false;
    for (struct NameTermList *field = term->record.fields; field; field = field->next) {
        if (field->name == NULL) {
            found_number = true;
            field->name = field_num_to_string(field_num++);
        } else {
            found_name = true;
        }
    }
    if (found_number && found_name) {
        report_mixed_positional_and_named_fields(term->location);
        tc_context->error = true;
        return NULL;
    }

    // second pass: check for duplicate fieldnames, and gather a list of field-types
    struct NameTypeList *field_types = NULL;
    struct NameTypeList **tail = &field_types;

    struct HashTable *found_field_names = new_hash_table();

    bool ok = true;

    for (struct NameTermList *field = term->record.fields; field; field = field->next) {

        if (hash_table_contains_key(found_field_names, field->name)) {
            report_duplicate_field_name(term->location, field->name);
            tc_context->error = true;
            ok = false;
        }

        hash_table_insert(found_field_names, field->name, NULL);

        struct NameTypeList *node = alloc(sizeof(struct NameTypeList));
        node->name = copy_string(field->name);
        node->type = copy_type(field->term->type);
        node->next = NULL;

        *tail = node;
        tail = &node->next;

        // if any field has NULL type, then the whole record is badly
        // typed
        if (field->term->type == NULL) {
            ok = false;
        }
    }

    free_hash_table(found_field_names);

    if (ok) {
        struct Type *type = make_type(term->location, TY_RECORD);
        type->record_data.fields = field_types;
        term->type = type;
    } else {
        free_name_type_list(field_types);
    }

    return NULL;
}

static void* typecheck_record_update(void *context, struct Term *term, void *type_result,
                                     void *lhs_result, void *fields_result)
{
    struct TypecheckContext *tc_context = context;

    // LHS must be a record type
    struct Type *lhs_ty = term->record_update.lhs->type;
    if (lhs_ty == NULL) {
        return NULL;
    }
    if (lhs_ty->tag != TY_RECORD) {
        report_updating_non_record(term->record_update.lhs->location);
        tc_context->error = true;
        return NULL;
    }

    bool ok = true;

    // For each update-field
    for (struct NameTermList *update = term->record_update.fields; update; update = update->next) {

        // Names must be given for all updates
        if (update->name == NULL) {
            report_field_name_missing(update->location);
            tc_context->error = true;
            ok = false;
            continue;
        }

        // Look for this field in the record type
        struct NameTypeList *search;
        for (search = lhs_ty->record_data.fields; search; search = search->next) {
            if (strcmp(search->name, update->name) == 0) {
                break;
            }
        }
        if (!search) {
            report_field_not_found(update->location, update->name);
            tc_context->error = true;
            ok = false;
            continue;
        }

        // Check the type matches
        if (!match_term_to_type(tc_context, search->type, &update->term)) {
            ok = false;
            continue;
        }

        // Check for duplicate field name
        for (struct NameTermList *prev_update = term->record_update.fields; prev_update != update; prev_update = prev_update->next) {
            if (prev_update->name && strcmp(prev_update->name, update->name) == 0) {
                report_duplicate_field_name(update->location, update->name);
                tc_context->error = true;
                ok = false;
            }
        }
    }

    if (ok) {
        // Result has same type as the original record
        term->type = copy_type(lhs_ty);
    }

    return NULL;
}

static void* typecheck_field_proj(void *context, struct Term *term, void *type_result,
                                  void *lhs_result)
{
    struct TypecheckContext *tc_context = context;

    struct Term *lhs = term->field_proj.lhs;
    const char *field_name = term->field_proj.field_name;

    if (lhs->type == NULL) {
        return NULL;
    }

    struct Type *record_type = chase_univars(lhs->type);

    if (record_type->tag == TY_RECORD) {
        // Check that the field name exists, and assign the proper type if so.
        for (struct NameTypeList *field = record_type->record_data.fields; field; field = field->next) {
            if (strcmp(field->name, field_name) == 0) {
                term->type = copy_type(field->type);
                return NULL;
            }
        }
        report_field_not_found(term->location, field_name);
        tc_context->error = true;

    } else {
        // LHS is not something we can project fields from.
        report_cannot_access_fields_in(lhs);
        tc_context->error = true;
    }

    return NULL;
}

static bool int_literal_in_range(struct Type *int_type, const char *str)
{
    uint64_t abs_value;
    bool negative;
    if (!string_to_int(str, &abs_value, &negative)) {
        return false;
    }

    return int_value_in_range(int_type->int_data.num_bits, int_type->int_data.is_signed, abs_value, negative);
}

static bool typecheck_pattern(struct TypecheckContext *tc_context, struct Pattern *pattern,
                              struct Type *scrutinee_type,
                              bool scrutinee_lvalue, bool scrutinee_read_only);

static bool typecheck_record_pattern(struct TypecheckContext *tc_context,
                                     struct Location location,
                                     struct NamePatternList *fields,
                                     struct Type *scrutinee_type,
                                     bool scrutinee_lvalue,
                                     bool scrutinee_read_only)
{
    // TODO: perhaps we could allow "punning" like in Ocaml.

    // first pass: number the positional fields,
    // and check for mixed positional and named fields
    bool found_number = false;
    bool found_name = false;
    int field_num = 0;
    for (struct NamePatternList *field = fields; field; field = field->next) {
        if (field->name == NULL) {
            found_number = true;
            field->name = field_num_to_string(field_num++);
        } else {
            found_name = true;
        }
    }
    if (found_number && found_name) {
        report_mixed_positional_and_named_fields(location);
        tc_context->error = true;
        return false;
    }

    // also in the case of numbered fields, check we have the correct number
    if (found_number) {
        int num_expected_fields = 0;
        for (struct NameTypeList *x = scrutinee_type->record_data.fields; x; x = x->next) {
            ++num_expected_fields;
        }
        if (num_expected_fields != field_num) {
            report_pattern_wrong_number_of_fields(location);
            tc_context->error = true;
            return false;
        }
    }

    // second pass: check the patterns, and check for duplicate fieldnames
    bool ok = true;

    struct HashTable *found_field_names = new_hash_table();

    for (struct NamePatternList *field = fields; field; field = field->next) {
        if (hash_table_contains_key(found_field_names, field->name)) {
            report_duplicate_field_name(location, field->name);
            tc_context->error = true;
            ok = false;
        }

        hash_table_insert(found_field_names, field->name, NULL);

        // Find the expected type of this field.
        struct NameTypeList *search = scrutinee_type->record_data.fields;
        while (search) {
            if (strcmp(search->name, field->name) == 0) {
                break;
            }
            search = search->next;
        }

        // If not found - error; otherwise - check the pattern matches the expected type.
        if (search == NULL) {
            report_field_not_found(field->pattern->location, field->name);
            tc_context->error = true;
            ok = false;
        } else if (!typecheck_pattern(tc_context, field->pattern, search->type,
                                      scrutinee_lvalue, scrutinee_read_only)) {
            ok = false;
        }
    }

    free_hash_table(found_field_names);

    return ok;
}

static bool typecheck_pattern(struct TypecheckContext *tc_context, struct Pattern *pattern,
                              struct Type *scrutinee_type,
                              bool scrutinee_lvalue, bool scrutinee_read_only)
{
    scrutinee_type = chase_univars(scrutinee_type);

    switch (pattern->tag) {
    case PAT_VAR:

        // no ref patterns in postconditions
        if (pattern->var.ref && tc_context->postcondition) {
            report_no_ref_in_postcondition(pattern->location);
            tc_context->error = true;
            return false;
        }

        // for ref pattern, scrutinee must be lvalue
        if (pattern->var.ref && !scrutinee_lvalue) {
            report_cannot_take_ref(pattern->location);
            tc_context->error = true;
            return false;
        }

        bool pat_read_only;
        if (pattern->var.ref) {
            // matching by ref - the ref inherits "read-onlyness" from the scrutinee
            pat_read_only = scrutinee_read_only;
        } else {
            // matching by value - allow changing the variable
            pat_read_only = false;
        }

        add_to_type_env(tc_context->type_env,
                        pattern->var.name,
                        copy_type(scrutinee_type),
                        !tc_context->executable,   // ghost
                        pat_read_only,             // read-only
                        false,                     // constructor
                        false);                    // impure
        return true;

    case PAT_BOOL:
        if (scrutinee_type->tag != TY_BOOL) {
            report_type_mismatch_pattern(scrutinee_type, pattern->location);
            tc_context->error = true;
            return false;
        } else {
            return true;
        }

    case PAT_INT:
        if (scrutinee_type->tag != TY_FINITE_INT) {
            report_type_mismatch_pattern(scrutinee_type, pattern->location);
            tc_context->error = true;
            return false;
        } else if (!int_literal_in_range(scrutinee_type, pattern->int_data.data)) {
            report_int_pattern_out_of_range(scrutinee_type, pattern->location);
            tc_context->error = true;
            return false;
        } else {
            return true;
        }

    case PAT_RECORD:
        if (scrutinee_type->tag != TY_RECORD) {
            report_type_mismatch_pattern(scrutinee_type, pattern->location);
            tc_context->error = true;
            return false;
        } else {
            return typecheck_record_pattern(tc_context, pattern->location, pattern->record.fields,
                                            scrutinee_type, scrutinee_lvalue, scrutinee_read_only);
        }

    case PAT_VARIANT:
        {
            if (scrutinee_type->tag != TY_VARIANT) {
                report_type_mismatch_pattern(scrutinee_type, pattern->location);
                tc_context->error = true;
                return false;
            }

            // Find out if this constructor requires a payload.
            // This is subtle because there is a difference between requiring a payload of {},
            // and not requiring a payload at all, but this cannot be found out by looking
            // at scrutinee_type, because scrutinee_type has already been converted to "Core"
            // form where a dummy payload of {} has been inserted (if applicable).
            // Instead we go looking for the constructor name in the environment.
            bool requires_payload = false;
            struct TypeEnvEntry * info = lookup_type_info(tc_context, pattern->variant.variant_name);
            if (info && info->constructor) {
                struct Type *ty = info->type;
                if (ty->tag == TY_FORALL) {
                    ty = ty->forall_data.type;
                }
                requires_payload = (ty->tag == TY_FUNCTION);
            }

            // We *can* use the scrutinee_type to see if this is a valid variant name
            // for the type, and to see what the payload_type should be.
            // Note: if payload_type ends up being NULL, this means that the variant
            // name is not correct for the scrutinee_type, i.e. a type error.
            struct Type *payload_type = NULL;
            for (struct NameTypeList *variant = scrutinee_type->variant_data.variants; variant; variant = variant->next) {
                if (strcmp(variant->name, pattern->variant.variant_name) == 0) {
                    payload_type = variant->type;
                    break;
                }
            }

            // has the user supplied a payload pattern?
            bool has_payload = (pattern->variant.payload != NULL);

            // Report errors
            if (payload_type == NULL || has_payload != requires_payload) {
                report_type_mismatch_pattern(scrutinee_type, pattern->location);
                tc_context->error = true;
                return false;
            }

            if (has_payload) {
                return typecheck_pattern(tc_context, pattern->variant.payload, payload_type,
                                         scrutinee_lvalue, scrutinee_read_only);
            } else {
                // we have a pattern w/o a payload (like "Red")
                // but in the core language (post-typechecking), all variants have a payload,
                // even if it is just {}, and all PAT_VARIANT patterns must match the
                // payload against something (var or wildcard).
                // in this case we don't care what the payload is so just wildcard it.
                pattern->variant.payload = make_pattern(pattern->location, PAT_WILDCARD);
                return true;
            }
        }

    case PAT_WILDCARD:
        return true;
    }

    fatal_error("typecheck_pattern: missing case");
}

static void* nr_typecheck_match(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct TypecheckContext *tc_context = context;

    // typecheck the scrutinee.
    transform_term(tr, context, term->match.scrutinee);

    // there must be at least one arm
    if (term->match.arms == NULL) {
        report_match_with_no_arms(term->location);
        tc_context->error = true;
    }

    struct Type * result_type = NULL;
    bool consistent_type = true;
    bool patterns_ok = true;

    // for each arm
    for (struct Arm *arm = term->match.arms; arm; arm = arm->next) {

        // check the pattern, add any pattern-variables into the environment
        if (term->match.scrutinee->type) {
            bool read_only = false;
            bool lvalue = is_lvalue(context, term->match.scrutinee, NULL, &read_only);
            if (!typecheck_pattern(context, arm->pattern, term->match.scrutinee->type,
                                   lvalue, read_only)) {
                patterns_ok = false;
            }
        }

        // check the rhs
        transform_term(tr, context, arm->rhs);

        // try to match the new arm's type to the previous one,
        // if applicable
        // TODO: This could be done better, i.e. we could try to match all the arms
        // to a common type (like we do with binop chains) instead of just matching
        // them all to the first arm's type.
        if (result_type) {
            if (!match_term_to_type(context, result_type, (struct Term **) &arm->rhs)) {
                consistent_type = false;
            }
        } else {
            result_type = ((struct Term*)arm->rhs)->type;
        }
    }

    if (term->match.scrutinee->type && patterns_ok && result_type && consistent_type) {
        term->type = copy_type(result_type);
    }

    return NULL;
}

static void* typecheck_sizeof(void *context, struct Term *term, void *type_result, void *rhs_result)
{
    struct TypecheckContext *tc_context = context;

    struct Term *rhs = term->sizeof_data.rhs;
    if (!rhs->type) {
        return NULL;
    }

    struct Type *array_type = chase_univars(rhs->type);

    if (array_type->tag != TY_ARRAY) {
        report_type_mismatch_string("array", rhs);
        tc_context->error = true;
        return NULL;
    }

    if (array_type->tag == TY_ARRAY
    && array_type->array_data.resizable
    && !is_lvalue(tc_context, rhs, NULL, NULL)
    && tc_context->executable) {
        // In executable code, passing an rvalue (of allocatable type)
        // to sizeof would "lose" the rvalue, so we would never be able
        // to free it.
        // In ghost code it is fine.
        report_cannot_take_sizeof(rhs);
        tc_context->error = true;
        return NULL;
    }

    int ndim = array_type->array_data.ndim;
    if (ndim == 1) {
        term->type = make_int_type(g_no_location, false, 64);
    } else {
        // tuple type
        struct NameTypeList *list = NULL;
        struct NameTypeList **tail = &list;
        char buf[30];
        for (int i = 0; i < ndim; ++i) {
            sprintf(buf, "%d", i);
            struct NameTypeList *node = alloc(sizeof(struct NameTypeList));
            node->name = copy_string(buf);
            node->type = make_int_type(g_no_location, false, 64);
            node->next = NULL;
            *tail = node;
            tail = &node->next;
        }
        term->type = make_type(g_no_location, TY_RECORD);
        term->type->record_data.fields = list;
    }

    return NULL;
}

static void * typecheck_allocated(void *context, struct Term *term, void *type_result, void *rhs_result)
{
    struct TypecheckContext *tc_context = context;

    struct Term *rhs = term->allocated.rhs;
    if (!rhs->type) {
        return NULL;
    }

    if (tc_context->executable) {
        report_executable_allocated(term);
        tc_context->error = true;
        return NULL;
    }

    struct Type *array_type = chase_univars(rhs->type);

    if (array_type->tag == TY_ARRAY
    && array_type->array_data.sizes == NULL
    && !array_type->array_data.resizable) {
        report_incomplete_array_type(term->location);
        tc_context->error = true;
        return NULL;
    }

    term->type = make_type(g_no_location, TY_BOOL);
    return NULL;
}

static void * typecheck_array_proj(void *context, struct Term *term, void *type_result, void *lhs_result, void *index_results)
{
    struct TypecheckContext *tc_context = context;

    // lhs must be an array
    struct Term *lhs = term->array_proj.lhs;

    if (lhs->type == NULL) {
        return NULL;
    }

    struct Type * array_type = chase_univars(lhs->type);

    if (array_type->tag != TY_ARRAY) {
        report_cannot_index(lhs);
        tc_context->error = true;
        return NULL;
    }

    // indexes are u64
    int num_indexes = 0;
    bool ok = true;

    struct Type *u64 = make_int_type(g_no_location, false, 64);

    for (struct OpTermList *node = term->array_proj.indexes; node; node = node->next) {
        if (node->rhs->type == NULL) {
            free_type(u64);
            return NULL;
        }

        if (!match_term_to_type(tc_context, u64, &node->rhs)) {
            ok = false;
        }

        ++num_indexes;
        if (num_indexes == INT_MAX) {
            fatal_error("ndim overflow");
        }
    }

    free_type(u64);

    if (num_indexes != array_type->array_data.ndim) {
        report_wrong_number_of_indexes(term);
        tc_context->error = true;
        ok = false;
    }

    if (ok) {
        term->type = copy_type(array_type->array_data.element_type);
    }

    return NULL;
}

// Typecheck a term.
// The term (and all its sub-terms) will either be given a type of
// kind * (valid according to the kind-checking rules), OR an error
// will be reported and the term's type will be set to NULL.
static void typecheck_term(struct TypecheckContext *tc_context, struct Term *term)
{
    struct TermTransform tr = {0};

    tr.transform_var = typecheck_var;
    tr.transform_bool_literal = typecheck_bool_literal;
    tr.transform_int_literal = typecheck_int_literal;
    tr.transform_string_literal = typecheck_string_literal;
    tr.transform_array_literal = typecheck_array_literal;
    tr.transform_cast = typecheck_cast;
    tr.transform_if = typecheck_if;
    tr.transform_unop = typecheck_unop;
    tr.transform_binop = typecheck_binop;
    tr.nr_transform_let = nr_typecheck_let;
    tr.nr_transform_quantifier = nr_typecheck_quantifier;
    tr.nr_transform_call = nr_typecheck_call;
    tr.nr_transform_tyapp = nr_typecheck_tyapp;
    tr.transform_record = typecheck_record;
    tr.transform_record_update = typecheck_record_update;
    tr.transform_field_proj = typecheck_field_proj;
    tr.nr_transform_match = nr_typecheck_match;
    tr.transform_sizeof = typecheck_sizeof;
    tr.transform_allocated = typecheck_allocated;
    tr.transform_array_proj = typecheck_array_proj;

    transform_term(&tr, tc_context, term);
}


// ----------------------------------------------------------------------------------------------------

//
// Attribute typechecking
//

static void typecheck_attributes(struct TypecheckContext *tc_context, struct Attribute *attr)
{
    bool found_ensures = false;

    while (attr) {

        if (found_ensures && attr->tag == ATTR_REQUIRES) {
            report_requires_after_ensures(attr);
            tc_context->error = true;
        }

        if (attr->tag == ATTR_ENSURES) {
            found_ensures = true;
        }

        switch (attr->tag) {
        case ATTR_REQUIRES:
        case ATTR_ENSURES:
        case ATTR_INVARIANT:
        case ATTR_DECREASES:

            if (attr->tag == ATTR_ENSURES) {
                tc_context->postcondition = true;
            }

            typecheck_term(tc_context, attr->term);

            if (attr->tag == ATTR_ENSURES) {
                tc_context->postcondition = false;
            }

            // requires, ensures, invariant must be bool
            // decreases must be int, bool, or tuple of those
            if (attr->tag != ATTR_DECREASES) {
                check_term_is_bool(tc_context, attr->term);
            } else {
                struct UnivarNode node;
                node.must_be_executable = false;
                node.must_be_complete = false;
                node.must_be_valid_decreases = true;
                ensure_type_meets_flags(tc_context, &node, attr->term->type, &attr->term->location);
            }

            break;

        }
        attr = attr->next;
    }
}


// ----------------------------------------------------------------------------------------------------

//
// Statement typechecking
//

static void typecheck_statements(struct TypecheckContext *tc_context,
                                 struct Statement *statements);

static bool contains_resizable_array_element(struct Term *term)
{
    if (term == NULL) {
        return false;
    }

    switch (term->tag) {
    case TM_FIELD_PROJ:
        return contains_resizable_array_element(term->field_proj.lhs);

    case TM_ARRAY_PROJ:
        // A[i]; need to check if A contains a ref to a resizable array
        // element, OR if A is a resizable array.
        // (Note that i containing a ref to a resizable array element is
        // fine, because the index is computed at the time the ref is taken,
        // and not recomputed afterwards.)
        return contains_resizable_array_element(term->array_proj.lhs)
            || (term->array_proj.lhs
                && term->array_proj.lhs->type
                && term->array_proj.lhs->type->tag == TY_ARRAY
                && term->array_proj.lhs->type->array_data.resizable);

    case TM_STRING_LITERAL:
        return false;

    case TM_VAR:
        // Even if the var is a ref, it would not contain any reference to a
        // resizable array element, so we are fine
        return false;

    default:
        // Not an lvalue, so there would have been a type error somewhere else
        // (trying to take ref to non-lvalue) and we can just return false here.
        return false;
    }
}

static void typecheck_var_decl_stmt(struct TypecheckContext *tc_context,
                                    struct Statement *stmt)
{
    // If there is no rhs and no type annotation, this is an error.
    if (!stmt->var_decl.type && !stmt->var_decl.rhs) {
        report_incomplete_definition(stmt->location);
        tc_context->error = true;
        return;
    }

    // If there is a type annotation, then kind-check it.
    if (stmt->var_decl.type) {
        if (!kindcheck_type(tc_context, &stmt->var_decl.type)) {
            return;
        }

        // In executable code, non-ref variables must have a "complete" type
        // (so that we know how much storage to allocate).
        if (tc_context->executable && !stmt->var_decl.ref) {
            struct UnivarNode node;
            node.must_be_executable = true;
            node.must_be_complete = true;
            node.must_be_valid_decreases = false;
            if (!ensure_type_meets_flags(tc_context, &node, stmt->var_decl.type, &stmt->var_decl.type->location)) {
                return;
            }
        }
    }

    // If there is a right-hand-side, then typecheck it.
    bool read_only = false;
    if (stmt->var_decl.rhs) {

        // If this is a ref, the rhs must be an lvalue (either read-only or read-write)
        if (stmt->var_decl.ref && !is_lvalue(tc_context, stmt->var_decl.rhs, NULL, &read_only)) {
            report_cannot_take_ref(stmt->var_decl.rhs->location);
            tc_context->error = true;
        }

        // typecheck rhs
        typecheck_term(tc_context, stmt->var_decl.rhs);
        if (stmt->var_decl.rhs->type) {

            if (stmt->var_decl.type) {
                // There is a type annotation. Ensure it is consistent with the rhs term.
                if (stmt->var_decl.ref) {
                    // "Refs" must match the type exactly, no casting allowed
                    unify_types(tc_context, stmt->var_decl.type, stmt->var_decl.rhs->type, &stmt->var_decl.rhs->location, true);
                } else {
                    // "Vars" are allowed to cast if required
                    match_term_to_type(tc_context, stmt->var_decl.type, &stmt->var_decl.rhs);
                }

            } else {
                // We are inferring a type.

                // Make sure it is not an incomplete type (in non-ref, executable case).
                if (tc_context->executable && !stmt->var_decl.ref) {
                    struct UnivarNode node;
                    node.must_be_executable = true;
                    node.must_be_complete = true;
                    node.must_be_valid_decreases = false;
                    if (!ensure_type_meets_flags(tc_context, &node, stmt->var_decl.rhs->type, &stmt->var_decl.rhs->location)) {
                        return;
                    }
                }

                // Add the inferred type annotation to the var decl statement.
                stmt->var_decl.type = copy_type(stmt->var_decl.rhs->type);
            }
        }

        // If this is a ref, the rhs must not be an element of a resizable array.
        if (stmt->var_decl.ref && contains_resizable_array_element(stmt->var_decl.rhs)) {
            report_cannot_take_ref_to_resizable_array_element(stmt->var_decl.rhs->location);
            tc_context->error = true;
        }

    } else {
        // If there is no right-hand-side, then manufacture one (as a DEFAULT expression)
        struct Term *default_rhs = make_term(stmt->location, TM_DEFAULT);
        default_rhs->type = copy_type(stmt->var_decl.type);
        stmt->var_decl.rhs = default_rhs;
    }

    // Add the new variable to the env (if typechecking was successful).
    if (stmt->var_decl.type) {
        add_to_type_env(tc_context->type_env,
                        stmt->var_decl.name,
                        copy_type(stmt->var_decl.type),    // handover
                        !tc_context->executable,  // ghost
                        read_only,                // read_only
                        false,                    // constructor
                        false);                   // impure
    }
}

static void typecheck_fix_stmt(struct TypecheckContext *tc_context,
                               struct Statement *stmt)
{
    stmt->ghost = true;

    struct Term *assert_term = tc_context->assert_term;
    if (assert_term == NULL) {
        report_fix_outside_proof(stmt);
        tc_context->error = true;

    } else if (!tc_context->at_proof_top_level) {
        report_fix_at_wrong_scope(stmt);
        tc_context->error = true;

    } else if (assert_term->tag != TM_QUANTIFIER || assert_term->quant.quant != QUANT_FORALL) {
        report_fix_no_forall_variable(stmt, assert_term);
        tc_context->error = true;

    } else if (!kindcheck_type(tc_context, &stmt->fix.type)) {
        // do nothing

    } else if (!unify_types(tc_context, assert_term->quant.type, stmt->fix.type, &stmt->location, true)) {
        // give an "extra" error message to show where the expected type came from
        report_fix_wrong_type(stmt, assert_term);
        tc_context->error = true;

    } else {
        // Move down one level inside the term (in case there is another "fix" later on!)
        tc_context->assert_term = assert_term->quant.body;

        add_to_type_env(tc_context->type_env,
                        stmt->fix.name,
                        copy_type(stmt->fix.type),    // handover
                        true,      // ghost
                        true,      // read_only
                        false,     // constructor
                        false);    // impure
    }
}

static void typecheck_obtain_stmt(struct TypecheckContext *tc_context,
                                  struct Statement *stmt)
{
    stmt->ghost = true;

    if (!kindcheck_type(tc_context, &stmt->obtain.type)) {
        return;
    }

    // for "obtain", the name is in scope within the condition-term
    // (as well as afterwards)
    add_to_type_env(tc_context->type_env,
                    stmt->obtain.name,
                    copy_type(stmt->obtain.type),   // handover
                    true,    // ghost
                    false,   // read_only
                    false,   // constructor
                    false);  // impure

    // the condition is not executable
    bool old_exec = tc_context->executable;
    tc_context->executable = false;

    typecheck_term(tc_context, stmt->obtain.condition);
    check_term_is_bool(tc_context, stmt->obtain.condition);

    tc_context->executable = old_exec;
}

static void typecheck_use_stmt(struct TypecheckContext *tc_context,
                               struct Statement *stmt)
{
    stmt->ghost = true;

    struct Term *assert_term = tc_context->assert_term;
    if (assert_term == NULL) {
        report_use_outside_proof(stmt);
        tc_context->error = true;

    } else if (!tc_context->at_proof_top_level) {
        report_use_at_wrong_scope(stmt);
        tc_context->error = true;

    } else if (assert_term->tag != TM_QUANTIFIER || assert_term->quant.quant != QUANT_EXISTS) {
        report_use_no_exists_variable(stmt, assert_term);
        tc_context->error = true;

    } else {
        // Typecheck the provided term - it should match the type in the quantifier
        typecheck_term(tc_context, stmt->use.term);
        if (stmt->use.term->type) {
            match_term_to_type(tc_context, assert_term->quant.type, &stmt->use.term);
        }

        // Move down one level inside the assert
        tc_context->assert_term = assert_term->quant.body;
    }
}

static void typecheck_assign_stmt(struct TypecheckContext *tc_context,
                                  struct Statement *stmt)
{
    // lhs should be a writable lvalue
    bool lhs_is_ghost_var = false;
    bool lhs_read_only = false;
    bool lvalue = is_lvalue(tc_context, stmt->assign.lhs, &lhs_is_ghost_var, &lhs_read_only);
    if (!lvalue) {
        report_cannot_assign(stmt->assign.lhs);
        tc_context->error = true;
    } else if (lhs_read_only) {
        report_cannot_assign_to_readonly(stmt->assign.lhs);
        tc_context->error = true;
    } else if (!lhs_is_ghost_var && !tc_context->executable) {
        // Note: typecheck_term reports the error if lhs is ghost
        // and we are in executable code.
        // Here we have to check the opposite error: writing nonghost
        // var from ghost code.
        report_writing_nonghost_from_ghost_code(stmt->location);
        tc_context->error = true;
    } else {
        // No ghost/readonly/lvalue related errors, so proceed with typechecking
        typecheck_term(tc_context, stmt->assign.lhs);
    }

    // Always typecheck the rhs
    typecheck_term(tc_context, stmt->assign.rhs);

    // The lhs and rhs types should match
    bool type_ok = match_term_to_type(tc_context, stmt->assign.lhs->type, &stmt->assign.rhs);

    // In executable code, we do not currently allow assignment of incomplete array
    // types (because the code generator would not produce the right code for it!).
    if (type_ok && tc_context->executable) {
        // Only the lhs type needs be checked (because both lhs and rhs have the same type
        // at this point).
        struct UnivarNode node;
        node.must_be_executable = true;
        node.must_be_complete = true;
        node.must_be_valid_decreases = false;
        ensure_type_meets_flags(tc_context, &node, stmt->assign.lhs->type, &stmt->assign.lhs->location);
    }
}

static void typecheck_swap_stmt(struct TypecheckContext *tc_context,
                                struct Statement *stmt)
{
    // both sides should be writable lvalues
    for (int i = 0; i < 2; ++i) {
        struct Term *term = (i == 0) ? stmt->swap.lhs : stmt->swap.rhs;

        bool ghost = false;
        bool read_only = false;
        bool lvalue = is_lvalue(tc_context, term, &ghost, &read_only);
        if (!lvalue) {
            report_cannot_swap(term);
            tc_context->error = true;
        } else if (read_only) {
            report_cannot_swap_readonly(term);
            tc_context->error = true;
        } else if (!ghost && !tc_context->executable) {
            report_writing_nonghost_from_ghost_code(term->location);
            tc_context->error = true;
        } else {
            typecheck_term(tc_context, term);
        }
    }

    // Both sides should have the same type.
    // Note: do not use match_term_to_type as we do not want to insert casts.
    // The types must match exactly.
    if (stmt->swap.lhs->type && stmt->swap.rhs->type) {
        unify_types(tc_context, stmt->swap.lhs->type, stmt->swap.rhs->type, &stmt->swap.rhs->location, true);
        if (tc_context->executable) {
            // Similarly to assignment, we do not currently allow code generation for
            // "swap A,B" where A and B are an incomplete array type (or contain one).
            struct UnivarNode node;
            node.must_be_executable = true;
            node.must_be_complete = true;
            node.must_be_valid_decreases = false;
            ensure_type_meets_flags(tc_context, &node, stmt->swap.lhs->type, &stmt->swap.lhs->location);
        }
    }
}

static void typecheck_return_stmt(struct TypecheckContext *tc_context,
                                  struct Statement *stmt)
{
    // there is a magic "return" variable in the local_env to indicate the return type
    struct TypeEnvEntry *return_info = lookup_type_info(tc_context, "return");

    if (!return_info) {
        // This can happen if the return-type couldn't be processed
        // (e.g. was 'real' in an executable context).
        // Just skip over the return-stmt in this case.
        return;
    }

    if (!tc_context->executable && !return_info->ghost) {
        report_cant_return_in_ghost_code(stmt);
        tc_context->error = true;

    } else if (return_info->type == NULL) {
        if (stmt->ret.value != NULL) {
            report_unexpected_return_value(stmt->ret.value);
            tc_context->error = true;
        }

    } else {
        if (stmt->ret.value == NULL) {
            report_missing_return_value(stmt);
            tc_context->error = true;
        } else {
            typecheck_term(tc_context, stmt->ret.value);
            match_term_to_type(tc_context, return_info->type, &stmt->ret.value);
        }
    }
}

static void typecheck_assert_stmt(struct TypecheckContext *tc_context,
                                  struct Statement *stmt)
{
    // asserts are always non-executable
    stmt->ghost = true;
    bool old_exec = tc_context->executable;
    tc_context->executable = false;

    struct Term *old_assert_term = tc_context->assert_term;
    tc_context->assert_term = stmt->assert_data.condition;

    typecheck_term(tc_context, stmt->assert_data.condition);
    check_term_is_bool(tc_context, stmt->assert_data.condition);

    if (stmt->assert_data.proof) {
        bool old_top_level = tc_context->at_proof_top_level;
        tc_context->at_proof_top_level = true;

        typecheck_statements(tc_context, stmt->assert_data.proof);

        tc_context->at_proof_top_level = old_top_level;
    }

    tc_context->executable = old_exec;
    tc_context->assert_term = old_assert_term;
}

static void typecheck_assume_stmt(struct TypecheckContext *tc_context,
                                  struct Statement *stmt)
{
    // assume stmts are always non-executable
    stmt->ghost = true;
    bool old_exec = tc_context->executable;
    tc_context->executable = false;

    typecheck_term(tc_context, stmt->assume.condition);
    check_term_is_bool(tc_context, stmt->assume.condition);

    tc_context->executable = old_exec;
}

static void typecheck_if_stmt(struct TypecheckContext *tc_context,
                              struct Statement *stmt)
{
    typecheck_term(tc_context, stmt->if_data.condition);
    check_term_is_bool(tc_context, stmt->if_data.condition);

    bool old_top_level = tc_context->at_proof_top_level;
    tc_context->at_proof_top_level = false;

    typecheck_statements(tc_context, stmt->if_data.then_block);
    typecheck_statements(tc_context, stmt->if_data.else_block);

    tc_context->at_proof_top_level = old_top_level;
}

static void typecheck_while_stmt(struct TypecheckContext *tc_context,
                                 struct Statement *stmt)
{
    typecheck_term(tc_context, stmt->while_data.condition);
    check_term_is_bool(tc_context, stmt->while_data.condition);

    // invariants, variants should be considered non-executable
    bool old_exec = tc_context->executable;
    tc_context->executable = false;
    typecheck_attributes(tc_context, stmt->while_data.attributes);
    tc_context->executable = old_exec;

    bool decreases_found = false;

    for (struct Attribute *attr = stmt->while_data.attributes; attr; attr = attr->next) {
        if (attr->tag != ATTR_INVARIANT && attr->tag != ATTR_DECREASES) {
            report_attribute_not_allowed_here(attr);
            tc_context->error = true;
        }

        if (attr->tag == ATTR_DECREASES) {
            if (decreases_found) {
                report_duplicate_decreases(attr);
                tc_context->error = true;
            } else {
                decreases_found = true;
            }
        }
    }

    if (!decreases_found) {
        report_missing_decreases(stmt->location);
        tc_context->error = true;
    }

    bool old_top_level = tc_context->at_proof_top_level;
    tc_context->at_proof_top_level = false;
    typecheck_statements(tc_context, stmt->while_data.body);
    tc_context->at_proof_top_level = old_top_level;
}

static void typecheck_call_stmt(struct TypecheckContext *tc_context,
                                struct Statement *stmt)
{
    typecheck_term(tc_context, stmt->call.term);
}

static void typecheck_match_stmt(struct TypecheckContext *tc_context,
                                 struct Statement *stmt)
{
    // typecheck the scrutinee
    typecheck_term(tc_context, stmt->match.scrutinee);

    bool old_top_level = tc_context->at_proof_top_level;
    tc_context->at_proof_top_level = false;

    // there must be at least one arm
    if (stmt->match.arms == NULL) {
        report_match_with_no_arms(stmt->location);
        tc_context->error = true;
    }

    // for each arm
    for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {

        // check the pattern, add any pattern-variables into the environment
        if (stmt->match.scrutinee->type) {
            bool read_only = false;
            bool lvalue = is_lvalue(tc_context, stmt->match.scrutinee, NULL, &read_only);
            typecheck_pattern(tc_context, arm->pattern, stmt->match.scrutinee->type,
                              lvalue, read_only);
        }

        // check the rhs
        typecheck_statements(tc_context, arm->rhs);
    }

    tc_context->at_proof_top_level = old_top_level;
}

static void typecheck_show_hide_stmt(struct TypecheckContext *tc_context,
                                     struct Statement *stmt)
{
    stmt->ghost = true;

    // Look up the name
    struct TypeEnvEntry * entry = lookup_type_info(tc_context, stmt->show_hide.name);

    if (entry == NULL) {
        tc_context->error = true;
        return;
    }

    if (entry->type == NULL) {
        fatal_error("missing type for variable, this is unexpected");
    }

    if (entry->type->tag == TY_FUNCTION) {
        // ok
    } else if (entry->type->tag == TY_FORALL && entry->type->forall_data.type->tag == TY_FUNCTION) {
        // ok
    } else {
        report_can_only_show_hide_functions(stmt->location);
        tc_context->error = true;
    }
}

static void typecheck_statements(struct TypecheckContext *tc_context,
                                 struct Statement *statements)
{
    // Check each statement individually
    struct Statement *stmt = statements;
    while (stmt) {

        bool old_exec = tc_context->executable;
        if (old_exec == false) {
            stmt->ghost = true;
        } else if (stmt->ghost) {
            tc_context->executable = false;
        }

        tc_context->statement = stmt;

        struct Statement *next_stmt = stmt->next;

        switch (stmt->tag) {
        case ST_VAR_DECL:
            typecheck_var_decl_stmt(tc_context, stmt);
            break;

        case ST_FIX:
            typecheck_fix_stmt(tc_context, stmt);
            break;

        case ST_OBTAIN:
            typecheck_obtain_stmt(tc_context, stmt);
            break;

        case ST_USE:
            typecheck_use_stmt(tc_context, stmt);
            break;

        case ST_ASSIGN:
            typecheck_assign_stmt(tc_context, stmt);
            break;

        case ST_SWAP:
            typecheck_swap_stmt(tc_context, stmt);
            break;

        case ST_RETURN:
            typecheck_return_stmt(tc_context, stmt);
            break;

        case ST_ASSERT:
            typecheck_assert_stmt(tc_context, stmt);
            break;

        case ST_ASSUME:
            typecheck_assume_stmt(tc_context, stmt);
            break;

        case ST_IF:
            typecheck_if_stmt(tc_context, stmt);
            break;

        case ST_WHILE:
            typecheck_while_stmt(tc_context, stmt);
            break;

        case ST_CALL:
            typecheck_call_stmt(tc_context, stmt);
            break;

        case ST_MATCH:
            typecheck_match_stmt(tc_context, stmt);
            break;

        case ST_MATCH_FAILURE:
            // this shouldn't be generated by the parser
            fatal_error("typecheck_statements: ST_MATCH_FAILURE: unexpected");

        case ST_SHOW_HIDE:
            typecheck_show_hide_stmt(tc_context, stmt);
            break;
        }

        stmt = next_stmt;

        tc_context->executable = old_exec;
        tc_context->statement = NULL;
    }
}


// ----------------------------------------------------------------------------------------------------

//
// Decl typechecking
//

static void typecheck_const_decl(struct TypecheckContext *tc_context,
                                 struct Decl *decl,
                                 bool implementation)
{
    if (decl->const_data.type) {
        if (!kindcheck_type(tc_context, &decl->const_data.type)) {
            return;
        }
    }

    // Const decls cannot be recursive
    if (decl->recursive) {
        report_illegal_recursion(decl);
        tc_context->error = true;

    } else {
        // If we have a term then let's typecheck it.
        if (decl->const_data.rhs != NULL) {
            typecheck_term(tc_context, decl->const_data.rhs);
        }

        if (decl->const_data.type != NULL && decl->const_data.rhs != NULL) {
            // There is both a type annotation, and a RHS.
            // Coerce the RHS to match the type annotation.
            match_term_to_type(tc_context, decl->const_data.type, &decl->const_data.rhs);

        } else if (decl->const_data.rhs != NULL) {
            // There is an RHS, but no type annotation.
            // Infer a type annotation from the term's type.
            decl->const_data.type = copy_type(decl->const_data.rhs->type);

        } else if (decl->const_data.type != NULL) {
            // Type annotation only, without a rhs.
            // Valid only in interface or ghost code.
            if (implementation && !decl->ghost) {
                report_incomplete_definition(decl->location);
                tc_context->error = true;
            }

        } else {
            // "const foo" with neither type annotation nor RHS term. This is invalid.
            report_incomplete_definition(decl->location);
            tc_context->error = true;
        }
    }

    if (decl->const_data.type) {

        remove_univars_from_decl(decl);

        add_to_type_env(tc_context->type_env->base,    // global env
                        decl->name,
                        copy_type(decl->const_data.type),     // handover
                        decl->ghost,
                        true,    // read_only
                        false,   // constructor
                        false);  // impure
    }
}

static void evaluate_constant(struct TypecheckContext *tc_context,
                              struct Decl *decl)
{
    if (decl->const_data.rhs && decl->const_data.rhs->type && !decl->ghost) {
        struct TypeEnvEntry *entry = lookup_type_info(tc_context, decl->name);
        if (entry) {
            struct Term *value = eval_to_normal_form(tc_context->type_env->base,  // global env
                                                     decl->const_data.rhs);
            if (value == NULL) {
                tc_context->error = true;
            } else {
                entry->value = value;
                decl->const_data.value = copy_term(value);
            }
        }
    }
}

static bool function_body_required(struct Decl *decl)
{
    // extern => no body required
    // ghost, without pre/post conditions => no body required
    // all other cases => a function body is required.
    return !(decl->function_data.is_extern
             || (decl->ghost && decl->attributes == NULL));
}

static bool function_body_allowed(struct Decl *decl)
{
    // extern => body not allowed
    // all other cases => a body can be supplied if wanted
    return !decl->function_data.is_extern;
}


static void typecheck_function_decl(struct TypecheckContext *tc_context,
                                    struct Decl *decl,
                                    bool implementation)
{
    // functions cannot be recursive currently
    if (decl->recursive) {
        report_illegal_recursion(decl);
        tc_context->error = true;
        return;
    }

    // ghost and extern are incompatible
    // ghost and impure are incompatible
    if (decl->ghost && decl->function_data.impure) {
        report_impure_cannot_be_ghost(decl);
        tc_context->error = true;
        return;
    }
    if (decl->ghost && decl->function_data.is_extern) {
        report_extern_cannot_be_ghost(decl);
        tc_context->error = true;
        return;
    }

    bool kinds_ok = true;

    for (struct TyVarList *tv = decl->function_data.tyvars; tv; tv = tv->next) {
        add_to_type_env(tc_context->type_env,   // local env
                        tv->name,
                        NULL,   // type (NULL for tyvars)
                        false,  // ghost
                        true,   // read_only
                        false,  // constructor
                        false); // impure
    }
    for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
        if (kindcheck_type(tc_context, &arg->type)) {
            add_to_type_env(tc_context->type_env,   // local env
                            arg->name,
                            copy_type(arg->type),   // handover
                            decl->ghost,
                            !arg->ref,      // read_only
                            false,          // constructor
                            false);         // impure
        } else {
            kinds_ok = false;
        }
    }

    // note: "return" still needs to be added to the env, even if the return_type is NULL,
    // because we need to know info->ghost
    struct Type *ret_type = decl->function_data.return_type;
    bool ret_type_ok = true;
    if (ret_type) {
        if (kindcheck_type(tc_context, &decl->function_data.return_type)) {
            ret_type = decl->function_data.return_type;

            if (tc_context->executable) {
                // Returning incomplete array types not currently supported, in executable contexts
                // (as we're not sure if the code generator will handle this correctly)
                struct UnivarNode node;
                node.must_be_executable = true;
                node.must_be_complete = true;
                node.must_be_valid_decreases = false;
                if (!ensure_type_meets_flags(tc_context, &node, ret_type, &ret_type->location)) {
                    ret_type_ok = false;
                }
            }

        } else {
            ret_type = NULL;
            kinds_ok = false;
            ret_type_ok = false;
        }
    }
    if (ret_type_ok) {
        add_to_type_env(tc_context->type_env,   // local env
                        "return",
                        copy_type(ret_type),   // handover
                        decl->ghost,
                        false,    // read_only
                        false,    // constructor
                        false);   // impure
    }

    // attributes are considered non-executable
    bool old_exec = tc_context->executable;
    tc_context->executable = false;
    typecheck_attributes(tc_context, decl->attributes);
    tc_context->executable = old_exec;

    for (struct Attribute *attr = decl->attributes; attr; attr = attr->next) {
        if (attr->tag != ATTR_REQUIRES && attr->tag != ATTR_ENSURES) {
            report_attribute_not_allowed_here(attr);
            tc_context->error = true;
        }
    }

    if (decl->function_data.body_specified) {
        if (decl->function_data.is_extern) {
            // body and extern are not allowed simultaneously
            report_both_body_and_extern(decl->location);
            tc_context->error = true;
        } else {
            // typecheck the function body
            typecheck_statements(tc_context, decl->function_data.body);
        }

    } else if (implementation && function_body_required(decl)) {
        report_incomplete_definition(decl->location);
        tc_context->error = true;
    }

    if (kinds_ok) {
        // Construct the function type and put it in the env
        struct Type *type = make_type(g_no_location, TY_FUNCTION);

        struct FunArg ** next_ptr = &type->function_data.args;
        for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
            *next_ptr = alloc(sizeof(struct FunArg));
            (*next_ptr)->name = NULL;
            (*next_ptr)->type = copy_type(arg->type);
            (*next_ptr)->ref = arg->ref;
            next_ptr = &((*next_ptr)->next);
        }
        *next_ptr = NULL;

        type->function_data.return_type = copy_type(ret_type);

        if (decl->function_data.tyvars) {
            struct Type *forall_type = make_type(g_no_location, TY_FORALL);
            forall_type->forall_data.tyvars = copy_tyvar_list(decl->function_data.tyvars);
            forall_type->forall_data.type = type;
            type = forall_type;
        }

        remove_univars_from_decl(decl);

        add_to_type_env(tc_context->type_env->base,   // global env
                        decl->name,
                        type,    // handover
                        decl->ghost,
                        true,    // read_only
                        false,   // constructor
                        decl->function_data.impure);
    }
}

static void replace_abstract_type_with_concrete(struct TypecheckContext *tc_context,
                                                const char *name,
                                                struct Type *new_type,
                                                bool implementation,
                                                struct DeclGroup *interface_decls)
{
    if (implementation) {
        struct TypeEnvEntry *prev_entry = lookup_type_info(tc_context, name);
        if (prev_entry && prev_entry->type == NULL && new_type != NULL) {
            substitute_type_in_decl_group(name, new_type, interface_decls);
        }
    }
}

static void typecheck_datatype_decl(struct TypecheckContext *tc_context,
                                    struct Decl *decl,
                                    bool implementation,
                                    struct DeclGroup *interface_decls)
{
    // datatypes cannot be recursive currently
    if (decl->recursive) {
        report_illegal_recursion(decl);
        tc_context->error = true;
        return;
    }

    bool kinds_ok = true;

    for (struct TyVarList *tyvar = decl->datatype_data.tyvars; tyvar; tyvar = tyvar->next) {
        add_to_type_env(tc_context->type_env,   // local env
                        tyvar->name,
                        NULL,
                        false,  // ghost
                        true,   // read_only
                        false,  // constructor
                        false); // impure
    }

    // kindcheck the payload types
    for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
        if (ctor->payload) {
            if (!kindcheck_type(tc_context, &ctor->payload)) {
                kinds_ok = false;
            }
        }
    }

    if (kinds_ok) {

        // Construct a TY_VARIANT with the correct variant names and payload types.
        struct Type *variant_type = make_type(decl->location, TY_VARIANT);
        variant_type->variant_data.variants = NULL;
        struct NameTypeList ** variant_tail = &variant_type->variant_data.variants;

        for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
            struct NameTypeList *variant = alloc(sizeof(struct NameTypeList));
            variant->name = copy_string(ctor->name);

            if (ctor->payload) {
                variant->type = copy_type(ctor->payload);
            } else {
                variant->type = make_type(ctor->location, TY_RECORD);
                variant->type->record_data.fields = NULL;
            }

            variant->next = NULL;

            *variant_tail = variant;
            variant_tail = &variant->next;
        }

        // If this datatype "overwrites" an abstract type ("type Foo;"),
        // then go back through the interface and rewrite all occurrences
        // of the abstract type to the concrete.
        replace_abstract_type_with_concrete(tc_context,
                                            decl->name,
                                            variant_type,
                                            implementation,
                                            interface_decls);

        // Add the datatype itself to the env (wrapping in TY_LAMBDA if necessary)
        struct Type * datatype = copy_type(variant_type);
        if (decl->datatype_data.tyvars) {
            struct Type * lambda_type = make_type(decl->location, TY_LAMBDA);
            lambda_type->lambda_data.tyvars = copy_tyvar_list(decl->datatype_data.tyvars);
            lambda_type->lambda_data.type = datatype;
            datatype = lambda_type;
        }
        add_to_type_env(tc_context->type_env->base,    // global env
                        decl->name,
                        datatype,      // handover
                        false,    // ghost
                        true,     // read_only
                        false,    // constructor
                        false);   // impure

        // Now add each constructor. We have to wrap the variant_type
        // in a function from the appropriate payload type (unless
        // there is no payload). We also have to add a TY_FORALL
        // wrapper if there are tyvars.
        struct DataCtor *ctor = decl->datatype_data.ctors;
        while (ctor) {
            struct Type * ctor_type = copy_type(variant_type);

            if (ctor->payload != NULL) {
                struct Type * func_type = make_type(decl->location, TY_FUNCTION);
                func_type->function_data.args = alloc(sizeof(struct FunArg));
                func_type->function_data.args->name = NULL;
                func_type->function_data.args->type = copy_type(ctor->payload);
                func_type->function_data.args->ref = false;
                func_type->function_data.args->next = NULL;
                func_type->function_data.return_type = ctor_type;
                ctor_type = func_type;
            }

            if (decl->datatype_data.tyvars) {
                struct Type * forall_type = make_type(decl->location, TY_FORALL);
                forall_type->forall_data.tyvars = copy_tyvar_list(decl->datatype_data.tyvars);
                forall_type->forall_data.type = ctor_type;
                ctor_type = forall_type;
            }

            add_to_type_env(tc_context->type_env->base,    // global env
                            ctor->name,
                            ctor_type,     // handover
                            false,   // ghost
                            true,    // read_only
                            true,    // constructor
                            false);  // impure

            ctor = ctor->next;
        }

        free_type(variant_type);

    } else {
        tc_context->error = true;
    }
}

static void typecheck_typedef_decl(struct TypecheckContext *tc_context,
                                   struct Decl *decl,
                                   bool implementation,
                                   struct DeclGroup *interface_decls)
{
    // typedefs cannot be recursive
    if (decl->recursive) {
        report_illegal_recursion(decl);
        tc_context->error = true;
        return;
    }

    // tyvars can only be used with typedefs, not abstract types
    if (decl->typedef_data.tyvars && decl->typedef_data.rhs == NULL) {
        report_abstract_type_with_tyvars(decl->location);
        tc_context->error = true;
        return;
    }

    bool kinds_ok = true;

    for (struct TyVarList *tyvar = decl->typedef_data.tyvars; tyvar; tyvar = tyvar->next) {
        add_to_type_env(tc_context->type_env,   // local env
                        tyvar->name,
                        NULL,
                        false,  // ghost
                        true,   // read_only
                        false,  // constructor
                        false); // impure
    }

    // kindcheck the rhs type (if applicable)
    if (decl->typedef_data.rhs && !kindcheck_type(tc_context, &decl->typedef_data.rhs)) {
        kinds_ok = false;
    }

    if (kinds_ok) {
        // construct the rhs type (wrapping in TY_LAMBDA if necessary)
        struct Type *ty = NULL;
        if (decl->typedef_data.rhs) {
            // (if rhs is NULL, this will become a new "tyvar" instead)
            ty = copy_type(decl->typedef_data.rhs);
        }
        if (decl->typedef_data.tyvars) {
            struct Type * lambda_type = make_type(decl->location, TY_LAMBDA);
            lambda_type->lambda_data.tyvars = copy_tyvar_list(decl->typedef_data.tyvars);
            lambda_type->lambda_data.type = ty;
            ty = lambda_type;
        }

        // If the type was previously abstract, but is now concrete,
        // then we now replace all instances of the abstract type in
        // interface decls with the concrete version.
        replace_abstract_type_with_concrete(tc_context,
                                            decl->name,
                                            ty,
                                            implementation,
                                            interface_decls);

        // Add this typedef (or abstract/extern type) to the type env.
        add_to_type_env(tc_context->type_env->base,    // global env
                        decl->name,
                        ty,
                        false,   // ghost
                        true,    // read_only
                        false,   // constructor
                        false);  // impure

        // Check the allocated-predicate, if there is one:
        if (decl->typedef_data.alloc_var) {

            // The type of the alloc_var is the typedef itself.
            if (decl->typedef_data.rhs) {
                fatal_error("this can't happen - parser won't create a typedef with both rhs and allocated");
            }
            ty = make_type(g_no_location, TY_VAR);
            ty->var_data.name = copy_string(decl->name);
            if (decl->typedef_data.tyvars != NULL) {
                fatal_error("this can't happen - abstract typedefs cannot have tyvars currently");
            }
            add_to_type_env(tc_context->type_env,   // local env
                            decl->typedef_data.alloc_var,
                            ty,
                            true,   // ghost
                            true,   // read_only
                            false,  // constructor
                            false); // impure

            // The type of the alloc_term should be bool.
            typecheck_term(tc_context, decl->typedef_data.alloc_term);
            check_term_is_bool(tc_context, decl->typedef_data.alloc_term);
            remove_univars_from_term(decl->typedef_data.alloc_term);
        }

    } else {
        tc_context->error = true;
    }
}

// This typechecks the decl and all "next" decls as well.
static void typecheck_decls(struct TypecheckContext *tc_context,
                            struct Decl *decls,
                            bool implementation,
                            struct DeclGroup *interface_decls)
{
    bool overall_error = tc_context->error;

    for (struct Decl *decl = decls; decl; decl = decl->next) {

        tc_context->error = false;

        // make a "local" type environment for the decl
        tc_context->type_env = push_type_env(tc_context->type_env);

        tc_context->executable =
            (decl->tag == DECL_CONST || decl->tag == DECL_FUNCTION)
            && !decl->ghost;

        tc_context->impure = false;
        if (decl->tag == DECL_FUNCTION) {
            tc_context->impure = decl->function_data.impure;
        }

        tc_context->temp_name_counter = 1;

        switch (decl->tag) {
        case DECL_CONST:
            typecheck_const_decl(tc_context, decl, implementation);
            if (!tc_context->error) {
                match_compiler_term(&tc_context->temp_name_counter, decl->const_data.rhs);
                evaluate_constant(tc_context, decl);
            }
            break;

        case DECL_FUNCTION:
            typecheck_function_decl(tc_context, decl, implementation);
            if (!tc_context->error) {
                // match compiler
                match_compiler_attributes(&tc_context->temp_name_counter, decl->attributes);
                match_compiler_statements(&tc_context->temp_name_counter, decl->function_data.body);
            }
            break;

        case DECL_DATATYPE:
            typecheck_datatype_decl(tc_context, decl, implementation, interface_decls);
            break;

        case DECL_TYPEDEF:
            if (implementation && decl->typedef_data.rhs == NULL && !decl->typedef_data.is_extern) {
                // "type Foo;" is only allowed in interface, not implementation
                report_abstract_type_in_impl(decl->location);
                tc_context->error = true;
            } else {
                typecheck_typedef_decl(tc_context, decl, implementation, interface_decls);
            }
            break;
        }

        if (tc_context->error) {
            overall_error = true;
        }

        // remove the local env
        tc_context->type_env = pop_type_env(tc_context->type_env);
    }

    tc_context->error = overall_error;
}

// This typechecks the DeclGroup and all "next" DeclGroups as well.
static void typecheck_decl_groups(struct TypecheckContext *tc_context,
                                  struct DeclGroup *groups,
                                  bool implementation,
                                  struct DeclGroup *interface_decls)
{
    for (struct DeclGroup *group = groups; group; group = group->next) {
        typecheck_decls(tc_context, group->decl, implementation, interface_decls);
    }
}


// ----------------------------------------------------------------------------------------------------

//
// Check interfaces match implementations
//

static bool int_impl_type_mismatch(const struct Type *lhs, const struct Type *rhs)
{
    if (!lhs && !rhs) {
        return false;
    }

    if (!lhs || !rhs) {
        return true;
    }

    if (!types_equal(lhs, rhs)) {
        return true;
    }

    return false;
}

// Check a 'const' interface and implementation to make sure they are compatible.
// Return false if not.
static bool check_interface_const(struct Module *module,
                                  struct Decl *interface,
                                  struct Decl *implementation)
{
    if (int_impl_type_mismatch(interface->const_data.type,
                               implementation->const_data.type)) {
        report_interface_mismatch_impl(interface);
        return false;
    }

    if (interface->const_data.rhs) {
        report_double_impl(interface);
        return false;
    }

    return true;
}

// Check a 'function' interface and implementation to make sure they are compatible.
static bool check_interface_function(struct Module *module,
                                     struct Decl *interface,
                                     struct Decl *implementation)
{
    struct TyVarList *tv1 = interface->function_data.tyvars;
    struct TyVarList *tv2 = implementation->function_data.tyvars;
    while (tv1 || tv2) {
        if (!(tv1 && tv2)) {
            // different numbers of tyvars
            report_interface_mismatch_impl(interface);
            return false;
        }

        if (strcmp(tv1->name, tv2->name) != 0) {
            // different tyvar names
            report_interface_mismatch_impl(interface);
            return false;
        }

        tv1 = tv1->next;
        tv2 = tv2->next;
    }

    struct FunArg *arg1 = interface->function_data.args;
    struct FunArg *arg2 = implementation->function_data.args;

    while (arg1 || arg2) {
        if (!(arg1 && arg2)) {
            // different numbers of arguments
            report_interface_mismatch_impl(interface);
            return false;
        }

        if (int_impl_type_mismatch(arg1->type, arg2->type)
        || arg1->ref != arg2->ref) {
            report_interface_mismatch_impl(interface);
            return false;
        }

        arg1 = arg1->next;
        arg2 = arg2->next;
    }

    if (int_impl_type_mismatch(interface->function_data.return_type,
                               implementation->function_data.return_type)) {
        report_interface_mismatch_impl(interface);
        return false;
    }

    if (interface->function_data.body_specified || !function_body_allowed(interface)) {
        report_double_impl(interface);
        return false;
    }

    if (!interface->function_data.impure && implementation->function_data.impure) {
        report_impurity_mismatch(interface);
        return false;
    }

    return true;
}

// Check an interface and implementation to make sure they are compatible.
// Return false if not.
static bool check_interface(struct Module *module,
                            struct Decl *interface,
                            struct Decl *implementation)
{
    // Special case: "type Foo;" in interface, and any type/datatype in
    // implementation, is allowed.
    if (interface->tag == DECL_TYPEDEF
    && interface->typedef_data.rhs == NULL
    && !interface->typedef_data.is_extern) {
        if (implementation->tag == DECL_TYPEDEF || implementation->tag == DECL_DATATYPE) {
            return true;
        } else {
            report_interface_mismatch_impl(interface);
            return false;
        }
    }

    // Otherwise, interface and implementation must always have same tag
    if (interface->tag != implementation->tag) {
        report_interface_mismatch_impl(interface);
        return false;
    }

    if (interface->ghost != implementation->ghost) {
        report_ghost_mismatch(interface);
        return false;
    }

    switch (interface->tag) {
    case DECL_CONST:
        // Two 'const' decls must be consistent (e.g. same type)
        return check_interface_const(module, interface, implementation);

    case DECL_FUNCTION:
        // Two 'function' decls must be consistent (e.g. same type)
        return check_interface_function(module, interface, implementation);

    case DECL_DATATYPE:
    case DECL_TYPEDEF:
        // Two 'datatype' or 'type' decls are not allowed, except for
        // the one "special case" given above (at the top of this
        // function).
        report_duplicate_definition(interface->name, interface->location);
        return false;
    }

    fatal_error("unknown interface tag");
}

// Returns true if this decl, when found in the 'interface' section, requires
// a separate implementation.
static bool requires_impl(struct Decl *interface)
{
    switch (interface->tag) {
    case DECL_CONST:
        // Impl only required for nonghost, and only if we don't
        // already have a rhs
        return !interface->ghost && interface->const_data.rhs == NULL;

    case DECL_FUNCTION:
        // Impl required only when (a) there is no function body given
        // in the interface already, and (b) the function does require
        // a body.
        return !interface->function_data.body_specified
            && function_body_required(interface);

    case DECL_DATATYPE:
        return false;

    case DECL_TYPEDEF:
        // A plain "type Foo;" requires an impl, but "extern type
        // Foo;" does not, nor does "type Foo = RHS;".
        return (interface->typedef_data.rhs == NULL && !interface->typedef_data.is_extern);
    }

    fatal_error("requires_impl failed");
}

// Check all interfaces to make sure they are compatible with any corresponding implementations.
// Return false if any problem found.
static bool check_interfaces(struct Module *module)
{
    bool all_ok = true;

    for (struct DeclGroup *int_group = module->interface; int_group; int_group = int_group->next) {
        for (struct Decl *int_decl = int_group->decl; int_decl; int_decl = int_decl->next) {

            bool found_impl = false;
            for (struct DeclGroup *imp_group = module->implementation;
            !found_impl && imp_group;
            imp_group = imp_group->next) {
                for (struct Decl *imp_decl = imp_group->decl;
                !found_impl && imp_decl;
                imp_decl = imp_decl->next) {
                    if (strcmp(imp_decl->name, int_decl->name) == 0) {
                        if (!check_interface(module, int_decl, imp_decl)) {
                            all_ok = false;
                        }
                        found_impl = true;
                    }
                }
            }

            if (!found_impl && requires_impl(int_decl)) {
                report_missing_impl(int_decl);
                all_ok = false;
            }
        }
    }

    return all_ok;
}


// ----------------------------------------------------------------------------------------------------

//
// Module typechecking
//

bool typecheck_module(TypeEnv *type_env,
                      struct Module *module,
                      bool interface_only)
{
    struct TypecheckContext tc_context;
    tc_context.type_env = type_env;
    tc_context.error = false;
    tc_context.executable = false;
    tc_context.impure = false;
    tc_context.statement = NULL;
    tc_context.assert_term = NULL;
    tc_context.at_proof_top_level = false;
    tc_context.postcondition = false;
    tc_context.temp_name_counter = 0;

    typecheck_decl_groups(&tc_context, module->interface, false, module->interface);

    if (!interface_only) {

        typecheck_decl_groups(&tc_context, module->implementation, true, module->interface);

        // Only check interfaces if typechecking succeeded
        if (!tc_context.error) {
            tc_context.error = !check_interfaces(module);
        }
    }

    return !tc_context.error;
}

bool typecheck_main_function(TypeEnv *type_env, const char *root_module_name)
{
    char *main_name = copy_string_2(root_module_name, ".main");

    struct TypeEnvEntry *entry = type_env_lookup(type_env, main_name);

    bool ok = (entry != NULL);
    if (!ok) {
        report_main_not_found(root_module_name);

    } else {

        ok = !entry->ghost
            && !entry->constructor
            && entry->type->tag == TY_FUNCTION
            && entry->type->function_data.args == NULL
            && entry->type->function_data.return_type == NULL;

        if (!ok) {
            report_main_wrong_type(root_module_name);
        }
    }

    free(main_name);
    return ok;
}
