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
#include "hash_table.h"
#include "match_compiler.h"
#include "names.h"
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
    // Type env for globals
    struct HashTable *global_env;

    // Type env for locals
    struct HashTable *local_env;

    // True if at least one type error has been detected
    bool error;

    // True if we are in executable code
    bool executable;

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
    struct TypeEnvEntry *entry = hash_table_lookup(context->local_env, name);
    if (entry == NULL) {
        entry = hash_table_lookup(context->global_env, name);
    }
    return entry;
}

static void free_type_env_entry(struct TypeEnvEntry *entry)
{
    free_type(entry->type);
    free_term(entry->value);
    free(entry);
}

static void remove_from_type_env(struct HashTable *env, const char *name)
{
    const char *key;
    void *value;
    hash_table_lookup_2(env, name, &key, &value);
    if (key) {
        hash_table_remove(env, key);
        free_type_env_entry(value);
        free((char*)key);
    }
}

void add_to_type_env(struct HashTable *env,
                     const char *name,    // copied
                     struct Type *type,   // handed over
                     bool ghost,
                     bool read_only,
                     bool constructor)
{
    remove_from_type_env(env, name);   // just in case there is an existing entry

    struct TypeEnvEntry *entry = alloc(sizeof(struct TypeEnvEntry));
    entry->type = type;
    entry->value = NULL;
    entry->ghost = ghost;
    entry->read_only = read_only;
    entry->constructor = constructor;

    hash_table_insert(env, copy_string(name), entry);
}

static void free_type_env_key_and_value(void *context, const char *key, void *value)
{
    free((char*)key);
    free_type_env_entry(value);
}

void free_type_env(struct HashTable *env)
{
    if (env) {
        hash_table_for_each(env, free_type_env_key_and_value, NULL);
        free_hash_table(env);
    }
}

// ----------------------------------------------------------------------------------------------------

// Type substitution

struct TypeSubstContext {
    struct TyVarList *tyvars;
    struct TypeList *tyargs;
};

static void * subst_ty_var(void *context, struct Type *type)
{
    struct TypeSubstContext *c = context;
    struct TyVarList *tyvars = c->tyvars;
    struct TypeList *tyargs = c->tyargs;

    while (tyvars) {
        if (strcmp(tyvars->name, type->var_data.name) == 0) {
            return copy_type(tyargs->type);
        }
        tyvars = tyvars->next;
        tyargs = tyargs->next;
    }

    return copy_type(type);
}

static void * subst_ty_forall_or_lambda(void *context, struct Type *type, void *tyvars_result, void *child_type_result)
{
    // to do this properly would require careful treatment of variable capture
    // luckily we do not need this for now
    fatal_error("substitute_in_type: unimplemented case");
}

static struct Type * substitute_in_type(struct TyVarList *tyvars,
                                        struct TypeList *tyargs,
                                        const struct Type *type)
{
    struct TypeSubstContext context;
    context.tyvars = tyvars;
    context.tyargs = tyargs;

    struct TypeTransform tr = {0};
    copying_type_transform(&tr);
    tr.transform_var = subst_ty_var;
    tr.transform_forall = subst_ty_forall_or_lambda;
    tr.transform_lambda = subst_ty_forall_or_lambda;

    return transform_type(&tr, &context, (struct Type*)type);
}


// ----------------------------------------------------------------------------------------------------

// Functions needed by TY_FIXED_ARRAY kind checking.

static void typecheck_term(struct TypecheckContext *tc_context, struct Term *term);

static bool match_term_to_type(struct TypecheckContext *tc_context,
                               struct Type *expected_type,
                               struct Term **term);

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
// number of *'s (including zero) on the left-hand side. Otherwise it
// behaves like kindcheck_type.
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

    case TY_FIXED_ARRAY:
        if (!kindcheck_type(tc_context, &(*type)->fixed_array_data.element_type)) {
            return false;
        }

        {
            // Array sizes are u64
            struct Type *u64 = make_int_type(g_no_location, false, 64);

            for (int i = 0; i < (*type)->fixed_array_data.ndim; ++i) {
                typecheck_term(tc_context, (*type)->fixed_array_data.sizes[i]);
                if ((*type)->fixed_array_data.sizes[i]->type == NULL) {
                    // Size doesn't typecheck
                    free_type(u64);
                    return false;
                }

                if (!match_term_to_type(tc_context, u64, &(*type)->fixed_array_data.sizes[i])) {
                    // Size doesn't have type u64
                    free_type(u64);
                    return false;
                }

                struct Term *normal = eval_to_normal_form(tc_context->global_env, (*type)->fixed_array_data.sizes[i]);
                if (normal == NULL) {
                    // Size is not a compile time constant
                    free_type(u64);
                    return false;
                }
                free_term((*type)->fixed_array_data.sizes[i]);
                (*type)->fixed_array_data.sizes[i] = normal;
            }

            free_type(u64);
        }

        return true;

    case TY_DYNAMIC_ARRAY:
        return kindcheck_type(tc_context, &(*type)->dynamic_array_data.element_type);

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
                substitute_in_type((*type)->app_data.lhs->lambda_data.tyvars,
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

    return true;
}


// ----------------------------------------------------------------------------------------------------

// Coerces 'term' so that it has same type as 'expected_type' (assumed a valid type of kind *).
// May modify 'term' by wrapping a cast around it.
// If error detected, prints msg and sets tc_context->error.
// Returns true if matching was successful.
static bool match_term_to_type(struct TypecheckContext *tc_context,
                               struct Type *expected_type,
                               struct Term **term)
{
    if (expected_type == NULL || (*term)->type == NULL) {
        // ignore errors in this case
        return true;
    }

    if (expected_type->tag != (*term)->type->tag) {
        report_type_mismatch(expected_type, *term);
        tc_context->error = true;
        return false;

    } else {

        switch (expected_type->tag) {
        case TY_VAR:
        case TY_BOOL:
        case TY_RECORD:
        case TY_VARIANT:
        case TY_FIXED_ARRAY:
        case TY_DYNAMIC_ARRAY:
        case TY_MATH_INT:
        case TY_MATH_REAL:
            if (!types_equal(expected_type, (*term)->type)) {
                report_type_mismatch(expected_type, *term);
                tc_context->error = true;
                return false;
            } else {
                return true;
            }
            break;

        case TY_FINITE_INT:
            if (expected_type->int_data.is_signed != (*term)->type->int_data.is_signed
            || expected_type->int_data.num_bits != (*term)->type->int_data.num_bits) {

                // Insert an implicit typecast to the expected type.
                struct Term *new_term = make_term((*term)->location, TM_CAST);
                new_term->type = copy_type(expected_type);
                new_term->cast.target_type = copy_type(expected_type);
                new_term->cast.operand = *term;
                *term = new_term;

            }
            return true;

        case TY_FUNCTION:
        case TY_FORALL:
            // Functions in complex exprs (e.g. "if-then-else") should not arise,
            // they should have produced another type error before now
            fatal_error("match_term_to_type: expected type cannot be TY_FUNCTION or TY_FORALL");

        case TY_LAMBDA:
        case TY_APP:
            // These should have been removed by kind-checking
            fatal_error("match_term_to_type called on non-kindchecked type");
        }
    }

    fatal_error("match_term_to_type: missing case");
}

// If term is not TY_BOOL, report error and return false.
// Otherwise, return true.
static bool check_term_is_bool(struct TypecheckContext *tc_context,
                               struct Term *term)
{
    if (term->type != NULL && term->type->tag != TY_BOOL) {
        struct Type dummy_bool_type;
        dummy_bool_type.location = g_no_location;
        dummy_bool_type.tag = TY_BOOL;
        report_type_mismatch(&dummy_bool_type, term);
        tc_context->error = true;
        return false;
    } else {
        return true;
    }
}

// If term is not TY_FINITE_INT, TY_MATH_INT, TY_BOOL, or a tuple of the
// same, report error and return false. Else return true.
static bool check_type_is_valid_for_decreases(struct TypecheckContext *tc_context,
                                              struct Type *type,
                                              const struct Location *location)
{
    if (type != NULL) {
        if (type->tag == TY_RECORD) {
            for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
                if (!isdigit((unsigned char)field->name[0])) {
                    // must be a tuple, not a record
                    report_invalid_decreases_type(*location);
                    tc_context->error = true;
                    return false;
                } else if (!check_type_is_valid_for_decreases(tc_context, field->type, location)) {
                    // member types of the tuple must be (recursively) valid
                    return false;
                }
            }
        } else if (type->tag != TY_FINITE_INT && type->tag != TY_MATH_INT && type->tag != TY_BOOL) {
            report_invalid_decreases_type(*location);
            tc_context->error = true;
            return false;
        }
    }
    return true;
}


// Helper for match_int_binop_types. Returns the "next bigger" size.
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

// Helper for check_binop_args.
// Tries to cast all TY_FINITE_INT terms in a (possibly chained) binop term to a common type.
// On success, wraps cast(s) arounds terms if required.
// On failure, logs error & sets tc_context->error.
static bool match_int_binop_types(struct TypecheckContext *tc_context, struct Term *term)
{
    struct TermData_BinOp *data = &term->binop;

    // We must use signed if any of the types are signed. Otherwise we stick to unsigned.
    bool need_signed = false;
    if (data->lhs->type->int_data.is_signed) {
        need_signed = true;
    } else {
        for (struct OpTermList *list = data->list; list; list = list->next) {
            if (list->rhs->type->int_data.is_signed) {
                need_signed = true;
                break;
            }
        }
    }

    // Now find out the size we need
    int num_bits_needed = data->lhs->type->int_data.num_bits;
    if (!data->lhs->type->int_data.is_signed && need_signed) {
        num_bits_needed = bigger_width(num_bits_needed);
    }
    for (struct OpTermList *list = data->list; list; list = list->next) {
        if (list->rhs->type == NULL) {
            return false;
        }
        int n = list->rhs->type->int_data.num_bits;
        if (!list->rhs->type->int_data.is_signed && need_signed) {
            n = bigger_width(n);
        }
        if (n > num_bits_needed) {
            num_bits_needed = n;
        }
    }

    if (num_bits_needed == 128) {
        // we don't support 128-bit types so this fails
        report_cannot_match_binop_types(term);
        tc_context->error = true;
        return false;
    }

    // Now we've found a target type that can accommodate all the terms,
    // we must insert casts as required.
    struct Type *expected_type = make_int_type(g_no_location, need_signed, num_bits_needed);
    match_term_to_type(tc_context, expected_type, &data->lhs);
    for (struct OpTermList *list = data->list; list; list = list->next) {
        match_term_to_type(tc_context, expected_type, &list->rhs);
    }
    free(expected_type);
    return true;
}

enum BinopCategory {
    BINOP_CAT_ANY_NON_FUNCTION,
    BINOP_CAT_BOOL_OR_NUMERIC,
    BINOP_CAT_NUMERIC,
    BINOP_CAT_ANY_INTEGER,
    BINOP_CAT_FINITE_INTEGER
};

// Checks that binop args are valid.
// If TY_FINITE_INT, cast all args to the same bitsize and signedness.
static bool check_binop_args(struct TypecheckContext *tc_context,
                             struct Term *binop,
                             enum BinopCategory cat)
{
    struct TermData_BinOp *data = &binop->binop;

    if (data->lhs->type == NULL) {
        return false;
    }

    const char *msg;
    switch (cat) {
    case BINOP_CAT_ANY_NON_FUNCTION:
        msg = "non-function type";
        break;

    case BINOP_CAT_BOOL_OR_NUMERIC:
        msg = "bool or numeric";
        break;

    case BINOP_CAT_NUMERIC:
        msg = "numeric type";
        break;

    case BINOP_CAT_ANY_INTEGER:
        msg = "integer";
        break;

    case BINOP_CAT_FINITE_INTEGER:
        msg = "finite-sized integer";
        break;
    }

    // Check the lhs
    bool lhs_ok = false;
    enum TypeTag lhs_tag = data->lhs->type->tag;

    switch (cat) {
    case BINOP_CAT_FINITE_INTEGER:
        lhs_ok = lhs_tag == TY_FINITE_INT;
        break;

    case BINOP_CAT_ANY_INTEGER:
        lhs_ok = lhs_tag == TY_FINITE_INT || lhs_tag == TY_MATH_INT;
        break;

    case BINOP_CAT_NUMERIC:
        lhs_ok = lhs_tag == TY_FINITE_INT || lhs_tag == TY_MATH_INT || lhs_tag == TY_MATH_REAL;
        break;

    case BINOP_CAT_BOOL_OR_NUMERIC:
        lhs_ok = lhs_tag == TY_FINITE_INT || lhs_tag == TY_MATH_INT || lhs_tag == TY_MATH_REAL || lhs_tag == TY_BOOL;
        break;

    case BINOP_CAT_ANY_NON_FUNCTION:
        lhs_ok = lhs_tag != TY_FUNCTION && lhs_tag != TY_FORALL;
        break;
    }

    if (!lhs_ok) {
        report_type_mismatch_string(msg, data->lhs);
        tc_context->error = true;
        return false;
    }

    // Check that all rhs terms have the same type as the lhs
    // (but allowing an inexact match in the case of TY_FINITE_INT).
    for (struct OpTermList *list = data->list; list; list = list->next) {
        if (list->rhs->type == NULL) {
            return false;
        }
        if (lhs_tag == TY_FINITE_INT) {
            if (list->rhs->type->tag != TY_FINITE_INT) {
                report_type_mismatch_string("finite-sized integer", list->rhs);
                tc_context->error = true;
                return false;
            }
        } else {
            if (!types_equal(data->lhs->type, list->rhs->type)) {
                report_type_mismatch(data->lhs->type, list->rhs);
                tc_context->error = true;
                return false;
            }
        }
    }

    // If the tag is TY_FINITE_INT, then cast them all to a uniform type.
    if (lhs_tag == TY_FINITE_INT) {
        match_int_binop_types(tc_context, binop);
    }

    return true;
}

// Check a type is valid for a variable i.e. it is not TY_FUNCTION or TY_FORALL.
// Also, in non-ghost code, make sure it is not TY_MATH_INT or TY_MATH_REAL.
// (precondition: the type should be valid, kind *)
static bool check_valid_var_type(struct TypecheckContext *tc_context, struct Location loc,
                                 struct Type *type)
{
    if (type == NULL) {
        // don't report further errors in this case
        return true;
    }

    switch (type->tag) {
    case TY_VAR:
    case TY_BOOL:
    case TY_FINITE_INT:
        return true;

    case TY_MATH_INT:
    case TY_MATH_REAL:
        if (tc_context->executable) {
            report_int_real_not_allowed(loc);
            tc_context->error = true;
            return false;
        } else {
            return true;
        }

    case TY_RECORD:
        for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
            if (!check_valid_var_type(tc_context, loc, field->type)) {
                return false;
            }
        }
        return true;

    case TY_VARIANT:
        for (struct NameTypeList *variant = type->variant_data.variants; variant; variant = variant->next) {
            if (!check_valid_var_type(tc_context, loc, variant->type)) {
                return false;
            }
        }
        return true;

    case TY_FIXED_ARRAY:
    case TY_DYNAMIC_ARRAY:
        return true;

    case TY_FUNCTION:
        report_function_variable_not_allowed(loc);
        tc_context->error = true;
        return false;

    case TY_FORALL:
        {
            int num_tyvars = tyvar_list_length(type->forall_data.tyvars);
            report_wrong_number_of_type_arguments(loc, num_tyvars, 0);
            tc_context->error = true;
        }
        return false;

    case TY_LAMBDA:
    case TY_APP:
        // this should be ruled out by kind-checking
        fatal_error("check_valid_var_type called on invalid type");
    }

    fatal_error("unrecognised type tag");
}


// ----------------------------------------------------------------------------------------------------

//
// Term typechecking
//

// Each term will be given a type of kind * (valid according to the
// kind-checking rules), OR an error will be reported and the term's
// type will be set to NULL.

static void* typecheck_var(void *context, struct Term *term, void *type_result)
{
    struct TypecheckContext *tc_context = context;

    // Look up the TypeEnvEntry for this variable name
    struct TypeEnvEntry * entry = lookup_type_info(tc_context, term->var.name);

    if (entry == NULL) {
        // This happens when there was an error with the original declaration
        // of the variable, so the variable never got inserted into the env.
        // Ignore any further errors relating to this variable.
        tc_context->error = true;
        return NULL;
    }

    if (entry->type == NULL) {
        fatal_error("missing type for variable, this is unexpected");
    }

    // Ghost variables can only be accessed from *nonexecutable* contexts
    if (entry->ghost && tc_context->executable) {
        report_access_ghost_var_from_executable_code(term);
        tc_context->error = true;
        return NULL;
    }

    // Term is OK, set the type.
    term->type = copy_type(entry->type);

    // If it is a constructor, change the term to TM_VARIANT, with a
    // {} (empty TM_RECORD) payload. This might not yet be
    // type-correct (e.g. if this variant carries a payload, and/or if
    // there are type arguments) but this will be fixed up later.
    if (entry->constructor) {
        const char *name = term->var.name;
        term->tag = TM_VARIANT;
        term->variant.variant_name = name;
        term->variant.payload = make_term(term->location, TM_RECORD);
        term->variant.payload->record.fields = NULL;
        term->variant.payload->type = make_type(g_no_location, TY_RECORD);
        term->variant.payload->type->record_data.fields = NULL;
    }

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
    // String literals currently have type u8[].
    // TODO: Maybe u8[N] (where N is the compile time known size of the
    // string) might make more sense?
    term->type = make_type(g_no_location, TY_DYNAMIC_ARRAY);
    term->type->dynamic_array_data.element_type = make_int_type(g_no_location, false, 8);
    term->type->dynamic_array_data.ndim = 1;
    return NULL;
}

static bool valid_cast_type(enum TypeTag tag, bool allow_math)
{
    return tag == TY_FINITE_INT
        || (allow_math && tag == TY_MATH_INT)
        || (allow_math && tag == TY_MATH_REAL);
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
    // In executable code, this is further restricted to just TY_FINITE_INT.

    enum TypeTag from_type = term->cast.operand->type->tag;
    enum TypeTag to_type = term->cast.target_type->tag;
    bool allow_math = !tc_context->executable;

    if (!valid_cast_type(from_type, allow_math) || !valid_cast_type(to_type, allow_math)) {
        if (valid_cast_type(from_type, true) && valid_cast_type(to_type, true)) {
            report_int_real_not_allowed(term->location);
        } else {
            report_invalid_cast(term);
        }
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

    bool branches_ok = check_valid_var_type(tc_context,
                                            term->if_data.then_branch->location,
                                            term->if_data.then_branch->type)
        && match_term_to_type(tc_context,
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

    bool numeric = operand->type->tag == TY_FINITE_INT
        || operand->type->tag == TY_MATH_INT
        || operand->type->tag == TY_MATH_REAL;

    bool is_signed = operand->type->tag != TY_FINITE_INT || operand->type->int_data.is_signed;

    switch (operator) {
    case UNOP_NEGATE:
        if (!numeric || !is_signed) {
            report_type_mismatch_string("signed numeric type", operand);
            tc_context->error = true;
            ok = false;
        }
        break;

    case UNOP_COMPLEMENT:
        if (operand->type->tag != TY_FINITE_INT) {
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
        term->type = copy_type(operand->type);
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

    if (term->binop.lhs->type == NULL || term->binop.list->rhs->type == NULL) {
        return NULL;
    }

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
                    cat = BINOP_CAT_ANY_NON_FUNCTION;
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

            if (term->binop.lhs->type->tag != TY_FINITE_INT) {
                report_type_mismatch_string("finite-sized integer", term->binop.lhs);
                tc_context->error = true;
                ok = false;
            }

            if (term->binop.list->rhs->type->tag != TY_FINITE_INT) {
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

    if (!check_valid_var_type(tc_context, term->let.rhs->location, term->let.rhs->type)) {
        return NULL;
    }

    add_to_type_env(tc_context->local_env,
                    term->let.name,
                    copy_type(term->let.rhs->type),   // handover
                    !tc_context->executable,   // ghost
                    true,                      // read-only
                    false);                    // constructor

    transform_term(tr, context, term->let.body);

    if (!check_valid_var_type(tc_context, term->let.body->location, term->let.body->type)) {
        return NULL;
    }

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

    add_to_type_env(tc_context->local_env,
                    term->quant.name,
                    copy_type(term->quant.type),     // handover
                    true,    // ghost
                    true,    // read-only
                    false);  // constructor

    transform_term(tr, context, term->quant.body);

    // Quantifier body must be boolean
    bool ok = check_term_is_bool(tc_context, term->quant.body);

    // Quantifier has type boolean
    if (ok) {
        term->type = make_type(g_no_location, TY_BOOL);
    }

    return NULL;
}

static void fix_up_ctor_app(struct Term *term, struct Type *term_type)
{
    // "Deconstruct" the term (note: term->type is already NULL)
    struct Term *func = term->call.func;
    struct OpTermList *args = term->call.args;

    // Deconstruct "args", take what we want and free the rest
    if (args == NULL || args->next) {
        fatal_error("Constructor application, unexpected no. of args found, was expecting exactly one");
    }
    struct Term *payload = args->rhs;
    free(args);

    // Deconstruct "func", similarly
    free_type(func->type);
    func->type = NULL;
    const char *variant_name = func->variant.variant_name;
    free_term(func->variant.payload);
    free(func);

    // Recreate the "func" in the main term
    term->tag = TM_VARIANT;
    term->type = term_type;
    term->variant.variant_name = variant_name;
    term->variant.payload = payload;
}


static void* typecheck_call(void *context, struct Term *term, void *type_result,
                            void *func_result, void *args_result)
{
    struct TypecheckContext *tc_context = context;

    struct Type * fun_type = term->call.func->type;
    if (fun_type == NULL) {
        return NULL;
    }

    bool ok = true;

    // The lhs must be of function type
    if (fun_type->tag != TY_FUNCTION) {

        // Error.

        // If the lhs has type TY_FORALL then count the number of expected tyargs
        // so we can give a better error message.

        if (fun_type->tag == TY_FORALL && fun_type->forall_data.type->tag == TY_FUNCTION) {
            report_wrong_number_of_type_arguments(term->call.func->location, tyvar_list_length(fun_type->forall_data.tyvars), 0);
        } else {
            report_call_of_non_function(term->call.func);
        }

        tc_context->error = true;
        ok = false;

    } else {

        // Check whether we are allowed to pass ref arguments
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

        // Special case: If the lhs term is a TM_VARIANT then we
        // should get rid of the TM_CALL, and apply the (single)
        // argument to the payload of the TM_VARIANT.
        if (ok && term->call.func->tag == TM_VARIANT) {
            fix_up_ctor_app(term, copy_type(fun_type->function_data.return_type));
            return NULL;
        }
    }

    if (ok) {
        term->type = copy_type(fun_type->function_data.return_type);
    }
    return NULL;
}

static void * typecheck_tyapp(void *context, struct Term *term, void *type_result,
                              void *lhs_result, void *tyargs_result)
{
    struct TypecheckContext *tc_context = context;

    if (!term->tyapp.lhs->type) {
        return NULL;
    }

    // Kind-check all type arguments and count them
    bool ok = true;
    int num_tyargs_present = 0;
    for (struct TypeList *tyarg = term->tyapp.tyargs; tyarg; tyarg = tyarg->next) {
        if (!kindcheck_type(tc_context, &tyarg->type)) {
            ok = false;
        }
        ++num_tyargs_present;
    }

    // Let's see if the lhs was expecting type arguments, and if so,
    // do we have the right number
    if (term->tyapp.lhs->type->tag != TY_FORALL) {
        report_wrong_number_of_type_arguments(term->location, 0, num_tyargs_present);
        tc_context->error = true;
        ok = false;
    } else {
        int num_tyargs_expected = tyvar_list_length(term->tyapp.lhs->type->forall_data.tyvars);
        if (num_tyargs_expected != num_tyargs_present) {
            report_wrong_number_of_type_arguments(term->location, num_tyargs_expected, num_tyargs_present);
            tc_context->error = true;
            ok = false;
        }
    }

    // The final type is constructed by substituting the type
    // arguments into the forall-type.
    if (ok) {
        term->type = substitute_in_type(term->tyapp.lhs->type->forall_data.tyvars,
                                        term->tyapp.tyargs,
                                        term->tyapp.lhs->type->forall_data.type);

        // If the LHS was a TM_VARIANT with a TY_FORALL type (i.e. a
        // constructor without its required type arguments), then we
        // now want to change it into a TM_VARIANT with whatever type
        // was underneath the TY_FORALL. term->type has now been set
        // correctly, but we need to strip away the TM_TYAPP wrapper
        // around the TM_VARIANT in this case.
        if (term->tyapp.lhs->tag == TM_VARIANT) {

            // strip down the current term
            // (but leaving term->type in place)
            free_type_list(term->tyapp.tyargs);
            struct Term *lhs = term->tyapp.lhs;
            const char *variant_name = lhs->variant.variant_name;
            struct Term *payload = lhs->variant.payload;
            free_type(lhs->type);
            free(lhs);

            // now reconstruct it as a TM_VARIANT
            term->tag = TM_VARIANT;
            term->variant.variant_name = variant_name;
            term->variant.payload = payload;
        }
    }

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

        // if any field has NULL type, or an invalid-for-var type,
        // then the whole record is badly typed
        if (field->term->type == NULL
        || !check_valid_var_type(tc_context,
                                 field->term->location,
                                 field->term->type)) {
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

    if (lhs->type->tag == TY_RECORD) {
        // Check that the field name exists, and assign the proper type if so.
        for (struct NameTypeList *field = lhs->type->record_data.fields; field; field = field->next) {
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

        add_to_type_env(tc_context->local_env,
                        pattern->var.name,
                        copy_type(scrutinee_type),
                        !tc_context->executable,   // ghost
                        pat_read_only,             // read-only
                        false);                    // constructor
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

    if (rhs->type->tag != TY_DYNAMIC_ARRAY && rhs->type->tag != TY_FIXED_ARRAY) {
        report_type_mismatch_string("array", rhs);
        tc_context->error = true;
        return NULL;
    }

    if (rhs->type->tag == TY_DYNAMIC_ARRAY
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

    int ndim = array_ndim(rhs->type);
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

    if (lhs->type->tag != TY_FIXED_ARRAY && lhs->type->tag != TY_DYNAMIC_ARRAY) {
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

    if (num_indexes != array_ndim(lhs->type)) {
        report_wrong_number_of_indexes(term);
        tc_context->error = true;
        ok = false;
    }

    if (ok) {
        term->type = copy_type(array_element_type(lhs->type));
    }

    return NULL;
}
    
static void typecheck_term(struct TypecheckContext *tc_context, struct Term *term)
{
    struct TermTransform tr = {0};

    tr.transform_var = typecheck_var;
    tr.transform_bool_literal = typecheck_bool_literal;
    tr.transform_int_literal = typecheck_int_literal;
    tr.transform_string_literal = typecheck_string_literal;
    tr.transform_cast = typecheck_cast;
    tr.transform_if = typecheck_if;
    tr.transform_unop = typecheck_unop;
    tr.transform_binop = typecheck_binop;
    tr.nr_transform_let = nr_typecheck_let;
    tr.nr_transform_quantifier = nr_typecheck_quantifier;
    tr.transform_call = typecheck_call;
    tr.transform_tyapp = typecheck_tyapp;
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
                check_type_is_valid_for_decreases(tc_context, attr->term->type, &attr->term->location);
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
                && term->array_proj.lhs->type->tag == TY_DYNAMIC_ARRAY);

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

        // Also ensure it is a valid var type.
        if (!check_valid_var_type(tc_context, stmt->var_decl.type->location, stmt->var_decl.type)) {
            return;
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
                match_term_to_type(tc_context, stmt->var_decl.type, &stmt->var_decl.rhs);

            } else if (check_valid_var_type(tc_context, stmt->var_decl.rhs->location, stmt->var_decl.rhs->type)) {
                // Add an inferred type annotation to the var decl statement.
                stmt->var_decl.type = copy_type(stmt->var_decl.rhs->type);
            }
        }

        // If this is a ref, the rhs must not be an element of a resizable array
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
        add_to_type_env(tc_context->local_env,
                        stmt->var_decl.name,
                        copy_type(stmt->var_decl.type),    // handover
                        !tc_context->executable,  // ghost
                        read_only,                // read_only
                        false);                   // constructor
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

    } else if (!types_equal(stmt->fix.type, assert_term->quant.type)) {
        report_fix_wrong_type(stmt, assert_term);
        tc_context->error = true;

    } else {
        // Move down one level inside the term (in case there is another "fix" later on!)
        tc_context->assert_term = assert_term->quant.body;

        add_to_type_env(tc_context->local_env,
                        stmt->fix.name,
                        copy_type(stmt->fix.type),    // handover
                        true,      // ghost
                        true,      // read_only
                        false);    // constructor
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
    add_to_type_env(tc_context->local_env,
                    stmt->obtain.name,
                    copy_type(stmt->obtain.type),   // handover
                    true,    // ghost
                    false,   // read_only
                    false);  // constructor

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
    match_term_to_type(tc_context, stmt->assign.lhs->type, &stmt->assign.rhs);
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
        if (!types_equal(stmt->swap.lhs->type, stmt->swap.rhs->type)) {
            report_type_mismatch(stmt->swap.lhs->type, stmt->swap.rhs);
            tc_context->error = true;
        }
    }
}

static void typecheck_return_stmt(struct TypecheckContext *tc_context,
                                  struct Statement *stmt)
{
    // there is a magic "return" variable in the local_env to indicate the return type
    struct TypeEnvEntry *return_info = lookup_type_info(tc_context, "return");

    if (!return_info) {
        fatal_error("return info not found in env");
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
    }

    if (!decl->recursive) {
        // If we have a term then let's typecheck it.
        // If we don't, and it's an interface (or ghost), leave it as NULL.
        // Otherwise error.
        if (decl->const_data.rhs != NULL) {
            typecheck_term(tc_context, decl->const_data.rhs);

        } else if (implementation && !decl->ghost) {
            report_incomplete_definition(decl->location);
            tc_context->error = true;
        }

        if (decl->const_data.type != NULL && decl->const_data.rhs != NULL) {
            // There is both a type annotation, and a RHS.
            // Coerce the RHS to match the type annotation.
            match_term_to_type(tc_context, decl->const_data.type, &decl->const_data.rhs);

        } else if (decl->const_data.rhs != NULL) {
            // There is an RHS, but no type annotation.
            // Infer a type annotation from the term's type.
            decl->const_data.type = copy_type(decl->const_data.rhs->type);
            check_valid_var_type(tc_context, decl->const_data.rhs->location, decl->const_data.type);

        } else if (decl->const_data.type == NULL) {
            // "const foo" with neither type annotation nor RHS term. This is invalid.
            report_incomplete_definition(decl->location);
            tc_context->error = true;
        }
    }

    if (decl->const_data.type) {
        add_to_type_env(tc_context->global_env,
                        decl->name,
                        copy_type(decl->const_data.type),     // handover
                        decl->ghost,
                        true,    // read_only
                        false);  // constructor
    }
}

static void evaluate_constant(struct TypecheckContext *tc_context,
                              struct Decl *decl)
{
    if (decl->const_data.rhs && decl->const_data.rhs->type && !decl->ghost) {
        struct TypeEnvEntry *entry = hash_table_lookup(tc_context->global_env, decl->name);
        if (entry) {
            struct Term *value = eval_to_normal_form(tc_context->global_env, decl->const_data.rhs);
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

    bool kinds_ok = true;

    for (struct TyVarList *tv = decl->function_data.tyvars; tv; tv = tv->next) {
        add_to_type_env(tc_context->local_env,
                        tv->name,
                        NULL,   // type (NULL for tyvars)
                        false,  // ghost
                        true,   // read_only
                        false); // constructor
    }
    for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
        if (kindcheck_type(tc_context, &arg->type)) {

            // arg types must be "valid for var" types
            bool old_exec = tc_context->executable;
            tc_context->executable = !decl->ghost;
            check_valid_var_type(tc_context, arg->type->location, arg->type);
            tc_context->executable = old_exec;

            add_to_type_env(tc_context->local_env,
                            arg->name,
                            copy_type(arg->type),   // handover
                            decl->ghost,
                            !arg->ref,      // read_only
                            false);         // constructor
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

            // return type must be "valid for var" type
            bool old_exec = tc_context->executable;
            tc_context->executable = !decl->ghost;
            check_valid_var_type(tc_context, ret_type->location, ret_type);
            tc_context->executable = old_exec;

        } else {
            ret_type = NULL;
            kinds_ok = false;
            ret_type_ok = false;
        }
    }
    if (ret_type_ok) {
        add_to_type_env(tc_context->local_env,
                        "return",
                        copy_type(ret_type),   // handover
                        decl->ghost,
                        false,    // read_only
                        false);   // constructor
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

        add_to_type_env(tc_context->global_env,
                        decl->name,
                        type,    // handover
                        decl->ghost,
                        true,    // read_only
                        false);  // constructor
    }
}

static void typecheck_datatype_decl(struct TypecheckContext *tc_context,
                                    struct Decl *decl)
{
    // datatypes cannot be recursive currently
    if (decl->recursive) {
        report_illegal_recursion(decl);
        tc_context->error = true;
        return;
    }

    bool kinds_ok = true;

    for (struct TyVarList *tyvar = decl->datatype_data.tyvars; tyvar; tyvar = tyvar->next) {
        add_to_type_env(tc_context->local_env,
                        tyvar->name,
                        NULL,
                        false,  // ghost
                        true,   // read_only
                        false); // constructor
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

        // Add the datatype itself to the env (wrapping in TY_LAMBDA if necessary)
        struct Type * datatype = copy_type(variant_type);
        if (decl->datatype_data.tyvars) {
            struct Type * lambda_type = make_type(decl->location, TY_LAMBDA);
            lambda_type->lambda_data.tyvars = copy_tyvar_list(decl->datatype_data.tyvars);
            lambda_type->lambda_data.type = datatype;
            datatype = lambda_type;
        }
        add_to_type_env(tc_context->global_env,
                        decl->name,
                        datatype,      // handover
                        false,    // ghost
                        true,     // read_only
                        false);   // constructor

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

            add_to_type_env(tc_context->global_env,
                            ctor->name,
                            ctor_type,     // handover
                            false,   // ghost
                            true,    // read_only
                            true);   // constructor

            ctor = ctor->next;
        }

        free_type(variant_type);

    } else {
        tc_context->error = true;
    }
}

static void typecheck_typedef_decl(struct TypecheckContext *tc_context,
                                   struct Decl *decl)
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
        add_to_type_env(tc_context->local_env,
                        tyvar->name,
                        NULL,
                        false,  // ghost
                        true,   // read_only
                        false); // constructor
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

        add_to_type_env(tc_context->global_env,
                        decl->name,
                        ty,
                        false,   // ghost
                        true,    // read_only
                        false);  // constructor
    } else {
        tc_context->error = true;
    }
}

// This typechecks the decl and all "next" decls as well.
static void typecheck_decls(struct TypecheckContext *tc_context,
                            struct Decl *decls,
                            bool implementation)
{
    bool overall_error = tc_context->error;

    for (struct Decl *decl = decls; decl; decl = decl->next) {

        tc_context->error = false;
        tc_context->local_env = new_hash_table();

        tc_context->executable = !decl->ghost;
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
            typecheck_datatype_decl(tc_context, decl);
            break;

        case DECL_TYPEDEF:
            typecheck_typedef_decl(tc_context, decl);
            break;
        }

        if (tc_context->error) {
            overall_error = true;
        }

        free_type_env(tc_context->local_env);
        tc_context->local_env = NULL;
    }

    tc_context->error = overall_error;
}

// This typechecks the DeclGroup and all "next" DeclGroups as well.
static void typecheck_decl_groups(struct TypecheckContext *tc_context,
                                  struct DeclGroup *groups,
                                  bool implementation)
{
    for (struct DeclGroup *group = groups; group; group = group->next) {
        typecheck_decls(tc_context, group->decl, implementation);
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

    return true;
}

// Check an interface and implementation to make sure they are compatible.
// Return false if not.
static bool check_interface(struct Module *module,
                            struct Decl *interface,
                            struct Decl *implementation)
{
    if (interface->tag != implementation->tag) {
        report_interface_mismatch_impl(interface);
        return false;
    }

    switch (interface->tag) {
    case DECL_CONST:
        return check_interface_const(module, interface, implementation);

    case DECL_FUNCTION:
        return check_interface_function(module, interface, implementation);

    case DECL_DATATYPE:
    case DECL_TYPEDEF:
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
    case DECL_TYPEDEF:
        return false;
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

static void remove_impl_only_names(struct HashTable *global_type_env,
                                   struct Module *module)
{
    // dummy values, for their address
    char NOTHING_IN_PARTICULAR;
    char IMPL_ONLY_CONSTANT;

    struct HashTable *int_names = new_hash_table();

    for (struct DeclGroup *int_group = module->interface; int_group; int_group = int_group->next) {
        for (struct Decl *int_decl = int_group->decl; int_decl; int_decl = int_decl->next) {

            void * info = &NOTHING_IN_PARTICULAR;
            if (int_decl->tag == DECL_CONST && int_decl->const_data.rhs == NULL) {
                info = &IMPL_ONLY_CONSTANT;
            }

            hash_table_insert(int_names, int_decl->name, info);
        }
    }

    for (struct DeclGroup *imp_group = module->implementation; imp_group; imp_group = imp_group->next) {
        for (struct Decl *imp_decl = imp_group->decl; imp_decl; imp_decl = imp_decl->next) {

            void *info = hash_table_lookup(int_names, imp_decl->name);
            if (info == NULL) {
                remove_from_type_env(global_type_env, imp_decl->name);

                switch (imp_decl->tag) {
                case DECL_CONST:
                case DECL_FUNCTION:
                case DECL_TYPEDEF:
                    // no additional names to remove
                    break;

                case DECL_DATATYPE:
                    // we must remove the ctor names as well
                    for (struct DataCtor *ctor = imp_decl->datatype_data.ctors; ctor; ctor = ctor->next) {
                        remove_from_type_env(global_type_env, ctor->name);
                    }
                    break;
                }

            } else if (info == &IMPL_ONLY_CONSTANT) {
                // This is a case like
                //   interface: const x: i32;
                //   implementation: const x: i32 = 1000;
                // Here we need to null out the 'value' field in the env, because, from
                // the perspective of other modules, the compile-time value of this constant
                // is unknown.
                // (Keep the value field in the decl, since we will need it for code generation.)
                struct TypeEnvEntry *entry = hash_table_lookup(global_type_env, imp_decl->name);
                free_term(entry->value);
                entry->value = NULL;
            }
        }
    }

    free_hash_table(int_names);
}


// ----------------------------------------------------------------------------------------------------

//
// Module typechecking
//

bool typecheck_module(struct HashTable *global_type_env,
                      struct Module *module,
                      bool interface_only,
                      bool keep_all)
{
    struct TypecheckContext tc_context;
    tc_context.global_env = global_type_env;
    tc_context.local_env = NULL;
    tc_context.error = false;
    tc_context.executable = false;
    tc_context.statement = NULL;
    tc_context.assert_term = NULL;
    tc_context.at_proof_top_level = false;
    tc_context.postcondition = false;
    tc_context.temp_name_counter = 0;

    typecheck_decl_groups(&tc_context, module->interface, false);

    if (!interface_only) {

        typecheck_decl_groups(&tc_context, module->implementation, true);

        // Only check interfaces if typechecking succeeded
        if (!tc_context.error) {
            tc_context.error = !check_interfaces(module);
        }

        if (!keep_all) {
            remove_impl_only_names(global_type_env, module);
        }
    }

    return !tc_context.error;
}

bool typecheck_main_function(struct HashTable *type_env, const char *root_module_name)
{
    char *main_name = copy_string_2(root_module_name, ".main");

    struct TypeEnvEntry *entry = hash_table_lookup(type_env, main_name);

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
