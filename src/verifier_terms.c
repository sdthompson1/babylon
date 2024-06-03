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
#include "sexpr.h"
#include "util.h"
#include "verifier.h"
#include "verifier_context.h"
#include "verifier_func.h"
#include "verifier_run.h"
#include "verifier_terms.h"
#include "verifier_types.h"

#include <ctype.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void bind_payload(struct VContext *context,
                  struct Term *scrutinee,
                  struct PatData_Variant *pat_data)
{
    if (scrutinee->type->tag != TY_VARIANT) {
        fatal_error("scrutinee has wrong type");
    }
    if (pat_data->payload == NULL || pat_data->payload->tag != PAT_VAR) {
        fatal_error("payload pattern is wrong");
    }
    if (!ref_chain_is_lvalue(scrutinee)) {
        // this should never trigger, because currently the match
        // compiler always replaces the scrutinee with a simple
        // variable (if it is not already such)
        fatal_error("scrutinee is not an lvalue");
    }

    uint32_t variant_num = 0;
    for (struct NameTypeList *v = scrutinee->type->variant_data.variants; v; v = v->next) {
        if (strcmp(v->name, pat_data->variant_name) == 0) {
            break;
        }
        ++variant_num;
    }

    struct RefChain * ref_scrut = ref_chain_for_term(context, scrutinee);

    struct RefChain * ref_payload = alloc(sizeof(struct RefChain));
    ref_payload->ref_type = RT_VARIANT;
    ref_payload->type = NULL;
    ref_payload->fol_type = verify_type(scrutinee->type);
    ref_payload->base = ref_scrut;
    ref_payload->index = variant_num;

    hash_table_insert(context->refs, pat_data->payload->var.name, ref_payload);
}

static struct Sexpr *convert_indexes(struct VContext *context,
                                     struct Location location,
                                     struct Type *array_type,
                                     struct OpTermList *indexes,
                                     struct Sexpr *fol_lhs,   // handover
                                     struct Sexpr *fol_type)
{
    const int ndim = array_type->array_data.ndim;

    struct Sexpr *result = NULL;

    if (ndim > 1) {
        result = make_list1_sexpr(array_index_type(ndim));
        struct Sexpr **tail = &result->right;
        for (struct OpTermList *index = indexes; index; index = index->next) {
            struct Sexpr *idx = verify_term(context, index->rhs);
            *tail = make_list1_sexpr(idx);
            tail = &(*tail)->right;
        }
    } else {
        result = verify_term(context, indexes->rhs);
    }

    struct Sexpr *size;

    if (array_type->array_data.sizes != NULL) {
        size = fixed_arr_size_sexpr(array_type);
        free_sexpr(fol_lhs);
    } else {
        size = make_string_sexpr("$FLD1");
        make_instance(&size, copy_sexpr(fol_type->right->right->left));
        size = make_list2_sexpr(size, fol_lhs);  // handover fol_lhs
    }
    fol_lhs = NULL;

    struct Sexpr *in_bounds = array_index_in_range(ndim, "$idx", "$size", indexes, false);
    in_bounds = make_list3_sexpr(
        make_string_sexpr("let"),
        make_list2_sexpr(
            make_list2_sexpr(
                make_string_sexpr("$idx"),
                copy_sexpr(result)),
            make_list2_sexpr(
                make_string_sexpr("$size"),
                size)),
        in_bounds);

    verify_condition(context, location, in_bounds, "array bounds", err_msg_out_of_bounds(location));
    free_sexpr(in_bounds);

    return result;
}

// Determine whether a term is an lvalue.
bool ref_chain_is_lvalue(const struct Term *term)
{
    switch (term->tag) {
    case TM_VAR:
        return true;

    case TM_FIELD_PROJ:
        return ref_chain_is_lvalue(term->field_proj.lhs);

    case TM_ARRAY_PROJ:
        return ref_chain_is_lvalue(term->array_proj.lhs);

    case TM_STRING_LITERAL:
    case TM_ARRAY_LITERAL:
        return true;

    case TM_CAST:
        return (term->type->tag == TY_ARRAY
                && ref_chain_is_lvalue(term->cast.operand));

    default:
        return false;
    }
}

// Make a new reference chain for an lvalue term.
// Should not return NULL.
struct RefChain *ref_chain_for_term(struct VContext *context, struct Term *term)
{
    switch (term->tag) {
    case TM_VAR:
        {
            struct RefChain *ref = hash_table_lookup(context->refs, term->var.name);
            if (ref) {
                validate_ref_chain(context, ref, term->location);
                return copy_ref_chain(ref);
            } else {
                ref = alloc(sizeof(struct RefChain));
                ref->ref_type = RT_LOCAL_VAR;
                ref->type = term->type;
                ref->fol_type = verify_type(term->type);
                ref->base = NULL;
                ref->variable_name = term->var.name;
                ref->postcond_new = term->var.postcond_new;
                return ref;
            }
        }
        break;

    case TM_FIELD_PROJ:
        {
            struct RefChain *base = ref_chain_for_term(context, term->field_proj.lhs);

            struct RefChain *ref = alloc(sizeof(struct RefChain));
            ref->ref_type = RT_FIELD;
            ref->type = NULL;
            ref->fol_type = verify_type(term->field_proj.lhs->type);
            ref->base = base;

            uint32_t index = 0;
            for (struct NameTypeList *node = term->field_proj.lhs->type->record_data.fields; node; node = node->next) {
                if (strcmp(node->name, term->field_proj.field_name) == 0) {
                    break;
                }
                ++index;
            }
            ref->index = index;

            return ref;
        }
        break;

    case TM_ARRAY_PROJ:
        {
            struct RefChain *base = ref_chain_for_term(context, term->array_proj.lhs);

            struct RefChain *ref = alloc(sizeof(struct RefChain));
            ref->ref_type = RT_ARRAY_ELEMENT;
            ref->type = NULL;
            ref->fol_type = verify_type(term->array_proj.lhs->type);
            ref->base = base;
            ref->array_index = NULL;
            ref->ndim = term->array_proj.lhs->type->array_data.ndim;
            ref->fixed_size = (term->array_proj.lhs->type->array_data.sizes != NULL);

            // we need a sexpr for the lhs so that we can get the size
            struct Sexpr *fol_lhs = ref_chain_to_sexpr(context, base);

            struct Sexpr *index =
                convert_indexes(context,
                                term->location,
                                term->array_proj.lhs->type,
                                term->array_proj.indexes,
                                fol_lhs,  // handover
                                ref->fol_type);
            ref->array_index = index;

            return ref;
        }
        break;

    case TM_STRING_LITERAL:
    case TM_ARRAY_LITERAL:
        {
            struct RefChain *ref = alloc(sizeof(struct RefChain));
            ref->ref_type = RT_SEXPR;
            ref->type = term->type;
            ref->fol_type = verify_type(term->type);
            ref->base = NULL;
            ref->sexpr = verify_term(context, term);
            return ref;
        }
        break;

    case TM_CAST:
        // Array casts are considered lvalues. Numeric casts are not.
        if (term->type->tag == TY_ARRAY) {
            struct RefChain *base = ref_chain_for_term(context, term->cast.operand);

            bool src_fixed = (term->cast.operand->type->array_data.sizes != NULL);
            bool dest_fixed = (term->type->array_data.sizes != NULL);

            if (src_fixed == dest_fixed) {
                // No cast required, as far as verifier is concerned
                return base;
            } else {
                struct RefChain *ref = alloc(sizeof(struct RefChain));
                ref->ref_type = RT_ARRAY_CAST;
                ref->type = term->type;
                ref->fol_type = verify_type(term->type);
                ref->base = base;
                return ref;
            }

        } else {
            fatal_error("ref_chain_for_term: not lvalue");
        }
        break;

    default:
        fatal_error("ref_chain_for_term: not lvalue");
    }
}

static struct Sexpr *translate_var(struct VContext *cxt, const char *var_name, bool postcond_new)
{
    // special case: "new" values of variables
    if (postcond_new) {
        struct Sexpr *sexpr = hash_table_lookup(cxt->new_values, var_name);
        if (sexpr) {
            return copy_sexpr(sexpr);
        }
    }

    const char *fol_name = lookup_local(cxt, var_name);

    if (fol_name) {
        if (hash_table_lookup(cxt->local_env, fol_name) == NULL) {
            fatal_error("unexpected: name not found in hash table");
        } else {
            return make_string_sexpr_handover(fol_name);
        }
    }

    // if we get here, it must be a global variable
    return make_string_sexpr_handover(copy_string_2("%", var_name));
}

// This shouldn't return NULL.
// Note: The caller should validate the reference (using validate_ref_chain) if it
// is not known to be valid. A reference created by ref_chain_for_term can be assumed
// to be valid just after it is created, but it might become invalid later on (e.g. if
// the variable being referred to gets modified by some future statement).
struct Sexpr *ref_chain_to_sexpr(struct VContext *cxt, struct RefChain *ref)
{
    switch (ref->ref_type) {
    case RT_LOCAL_VAR:
        return translate_var(cxt, ref->variable_name, ref->postcond_new);

    case RT_FIELD:
    case RT_VARIANT:
        {
            struct Sexpr *base = ref_chain_to_sexpr(cxt, ref->base);

            const char *prefix = ref->ref_type == RT_FIELD ? "$FLD" : "$INF";
            char selector[30];
            sprintf(selector, "%s%" PRIu32, prefix, ref->index);

            struct Sexpr *expr = make_string_sexpr(selector);

            // fol_type is either (instance $PROD (types)), or (instance $SUM (types))
            // either way, the type-list is fol_type->right->right->left
            make_instance(&expr, copy_sexpr(ref->fol_type->right->right->left));

            return make_list2_sexpr(expr, base);
        }

    case RT_ARRAY_ELEMENT:
        {
            struct Sexpr *base = ref_chain_to_sexpr(cxt, ref->base);

            struct Sexpr *expr;
            if (ref->fixed_size) {
                expr = base;
            } else {
                // $FLD0 gives the array itself
                expr = make_string_sexpr("$FLD0");
                make_instance(&expr, copy_sexpr(ref->fol_type->right->right->left));
                expr = make_list2_sexpr(expr, base);
            }

            // now use select to do the indexing
            return make_list3_sexpr(make_string_sexpr("select"),
                                    expr,
                                    copy_sexpr(ref->array_index));
        }

    case RT_ARRAY_CAST:
        // This shouldn't be needed (because array-casts only appear
        // in function actual arguments currently, and we shouldn't be
        // calling ref_chain_to_sexpr on those.)
        fatal_error("ref_chain_to_sexpr: RT_ARRAY_CAST: not implemented");

    case RT_SEXPR:
        return copy_sexpr(ref->sexpr);
    }

    fatal_error("ref_chain_to_sexpr: invalid ref_type");
}

static struct Sexpr *ref_chain_to_atomic_sexpr(struct VContext *cxt,
                                               struct RefChain *ref,
                                               struct Sexpr *fol_type)  // will be copied
{
    struct Sexpr *expr = ref_chain_to_sexpr(cxt, ref);
    if (expr->type != S_STRING) {
        uintptr_t unique_num = (uintptr_t) hash_table_lookup(cxt->local_counter, "$RefUpdate");
        hash_table_insert(cxt->local_counter, "$RefUpdate", (void*)(unique_num + 1));
        char unique_suffix[60];
        sprintf(unique_suffix, "%" PRIuPTR, unique_num);

        const char *name = copy_string_2("$RefLHS.", unique_suffix);
        add_const_item(cxt,
                       copy_string(name),
                       NULL,
                       copy_sexpr(fol_type),
                       expr,   // handover
                       true);
        return make_string_sexpr_handover(name);
    } else {
        return expr;
    }
}

// Validate that a reference is valid - e.g. that the array hasn't been resized
// or the variant hasn't been changed to a different tag.
void validate_ref_chain(struct VContext *context,
                        struct RefChain *ref,
                        struct Location location)
{
    switch (ref->ref_type) {
    case RT_LOCAL_VAR:
        break;

    case RT_FIELD:
        validate_ref_chain(context, ref->base, location);
        break;

    case RT_VARIANT:
        {
            validate_ref_chain(context, ref->base, location);

            // Validate that the LHS is still of the same variant
            struct Sexpr *base = ref_chain_to_sexpr(context, ref->base);

            char selector[30];
            sprintf(selector, "$IN%" PRIu32, ref->index);

            struct Sexpr *expr = make_string_sexpr(selector);
            make_instance(&expr, copy_sexpr(ref->fol_type->right->right->left));

            expr = make_list2_sexpr(
                make_list3_sexpr(
                    make_string_sexpr("_"),
                    make_string_sexpr("is"),
                    expr),
                base);
            base = NULL;

            verify_condition(context, location, expr, "variant ref valid",
                             err_msg_ref_invalid_variant_change(location));

            free_sexpr(expr);
            expr = NULL;
        }
        break;

    case RT_ARRAY_ELEMENT:
        validate_ref_chain(context, ref->base, location);

        // Refs to elements of resizable arrays are now illegal
        // so there is nothing further to check
        break;

    case RT_ARRAY_CAST:
        // Nothing to check here.
        validate_ref_chain(context, ref->base, location);

    case RT_SEXPR:
        // We assume RT_SEXPR is only used in cases where the
        // underlying s-expression can never become invalid. At the
        // time of writing, RT_SEXPR is only used for string literals,
        // so this should be correct.
        break;
    }
}

// Update the target of the given reference chain to contain 'rhs'.
// Note: similarly to ref_chain_to_sexpr, the caller must be sure that the RefChain is valid.
void update_reference(struct VContext *context,
                      struct RefChain *ref,   // shared
                      struct Sexpr *rhs)      // handed over
{
    switch (ref->ref_type) {
    case RT_LOCAL_VAR:
        update_local(context,
                     ref->variable_name,
                     NULL,
                     copy_sexpr(ref->fol_type),
                     rhs);
        break;

    case RT_FIELD:
        {
            // Get a pointer to the list of field-types
            // Note: ref->fol_type is (instance $PROD types)
            struct Sexpr *field_types = ref->fol_type->right->right->left;

            // Make an expression for the LHS of the field-projection
            // (If this is a complex expression, give it a name, to reduce duplication)
            struct Sexpr *lhs = ref_chain_to_atomic_sexpr(context, ref->base, ref->fol_type);

            // Now set <LHS> to {<LHS> with <field> set to <RHS>}
            struct Sexpr *new_lhs = copy_record_fields(lhs, field_types);

            uint32_t idx = 0;
            bool found = false;
            for (struct Sexpr *fld = new_lhs->right; fld; fld = fld->right) {
                if (idx == ref->index) {
                    free_sexpr(fld->left);
                    fld->left = rhs;
                    found = true;
                    break;
                }
                ++idx;
            }
            if (!found) {
                fatal_error("update_reference failed");
            }

            free_sexpr(lhs);
            lhs = NULL;
            update_reference(context,
                             ref->base,
                             new_lhs);    // handover
        }
        break;

    case RT_VARIANT:
        {
            struct Sexpr *variant_types = ref->fol_type->right->right->left;

            char name[30];
            sprintf(name, "$IN%" PRIu32, ref->index);
            struct Sexpr *inject = make_string_sexpr(name);
            make_instance(&inject, copy_sexpr(variant_types));

            update_reference(context, ref->base,
                             make_list2_sexpr(inject, rhs));
        }
        break;

    case RT_ARRAY_ELEMENT:
        {
            struct Sexpr *lhs = ref_chain_to_atomic_sexpr(context, ref->base, ref->fol_type);

            struct Sexpr *update = NULL;

            if (ref->fixed_size) {
                update = make_list4_sexpr(
                    make_string_sexpr("store"),
                    lhs,
                    copy_sexpr(ref->array_index),
                    rhs);

            } else {
                struct Sexpr *field_types = ref->fol_type->right->right->left;
                struct Sexpr *prod = make_string_sexpr("$PROD");
                struct Sexpr *fld0 = make_string_sexpr("$FLD0");
                struct Sexpr *fld1 = make_string_sexpr("$FLD1");
                make_instance(&prod, copy_sexpr(field_types));
                make_instance(&fld0, copy_sexpr(field_types));
                make_instance(&fld1, copy_sexpr(field_types));

                struct Sexpr *updated_array = make_list4_sexpr(
                    make_string_sexpr("store"),
                    make_list2_sexpr(fld0, copy_sexpr(lhs)),
                    copy_sexpr(ref->array_index),
                    rhs);

                update = make_list3_sexpr(prod, updated_array, make_list2_sexpr(fld1, lhs));
            }

            update_reference(context, ref->base, update);
        }
        break;

    case RT_ARRAY_CAST:
        if (ref->type->array_data.sizes != NULL) {
            // ref r: T[n] = <some array descriptor>
            // We are given a new array (T[n]). We need to construct
            // ($PROD array size) and use that to update the base.

            // ref->fol_type is something like (Array idx-type elem-type).

            struct Sexpr *prod_ctor =
                make_list3_sexpr(
                    make_string_sexpr("instance"),
                    make_string_sexpr("$PROD"),
                    make_list2_sexpr(
                        copy_sexpr(ref->fol_type),
                        copy_sexpr(ref->fol_type->right->left)));

            struct Sexpr *tuple = make_list3_sexpr(prod_ctor,
                                                   rhs,
                                                   fixed_arr_size_sexpr(ref->type));

            update_reference(context, ref->base, tuple);

        } else {
            // ref r: T[] = <some array of size n>
            // We are given a new descriptor (T[]). We need to extract the
            // array ($FLD0) and use that to update the base.

            // ref->fol_type is (instance $PROD (array-type size-type)).

            struct Sexpr *arr = copy_sexpr(ref->fol_type);
            free_sexpr(arr->right->left);
            arr->right->left = make_string_sexpr("$FLD0");
            arr = make_list2_sexpr(arr, rhs);

            update_reference(context, ref->base, arr);
        }
        break;

    case RT_SEXPR:
        fatal_error("trying to update const reference");

    default:
        fatal_error("update_reference unimplemented case");
    }
}

static void* verify_var(void *context, struct Term *term, void *type_result)
{
    struct VContext *cxt = context;
    struct RefChain *ref = hash_table_lookup(cxt->refs, term->var.name);
    if (ref) {
        // reference variable
        validate_ref_chain(cxt, ref, term->location);
        return ref_chain_to_sexpr(context, ref);
    } else {
        // normal local variable
        return translate_var(context, term->var.name, term->var.postcond_new);
    }
}

static struct Sexpr *make_default(struct VContext *cxt, struct Type *type);

static struct Sexpr *make_default_fixed_array(struct VContext *cxt,
                                              struct Type *array_type)
{
    const char *key = "$DefaultArrayNum";
    void *value = hash_table_lookup(cxt->string_names, key);
    uintptr_t unique_num = (uintptr_t)value;
    hash_table_insert(cxt->string_names, key, (void*)(unique_num + 1));

    char name[60];
    sprintf(name, "$DfltArr.%s.%" PRIuPTR, cxt->current_decl_name, unique_num);

    struct Sexpr *fol_type = verify_type(array_type);

    // this says that each in-range element of "$arr" is equal to the
    // default, and out-of-range elements are equal to $ARBITRARY
    struct Sexpr *equality =
        for_all_array_elt(
            array_type->array_data.ndim,
            make_list3_sexpr(
                make_string_sexpr("="),
                make_string_sexpr("$elt"),
                make_default(cxt, array_type->array_data.element_type)),
            verify_type(array_type->array_data.element_type));

    // to make the axiom we need to use "let" to assign values for
    // $arr and $size
    struct Sexpr *axioms =
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr("assert"),
                make_list3_sexpr(
                    make_string_sexpr("let"),
                    make_list2_sexpr(
                        make_list2_sexpr(
                            make_string_sexpr("$arr"),
                            make_string_sexpr(name)),
                        make_list2_sexpr(
                            make_string_sexpr("$size"),
                            fixed_arr_size_sexpr(array_type))),
                    equality)));

    // make an Item for the array
    struct Item *item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));

    item->fol_decl = make_list3_sexpr(
        make_string_sexpr("declare-const"),
        make_string_sexpr(name),
        copy_sexpr(fol_type));

    item->fol_axioms = axioms;

    item->fol_name = copy_string(name);

    item->fol_type = fol_type;
    fol_type = NULL;

    hash_table_insert(cxt->global_env, copy_string(name), item);

    return make_string_sexpr(name);
}

static struct Sexpr *make_default(struct VContext *cxt, struct Type *type)
{
    switch (type->tag) {
    case TY_VAR:
        return make_string_sexpr_handover(copy_string_2("$default-%", type->var_data.name));

    case TY_BOOL:
        return make_string_sexpr("false");

    case TY_FINITE_INT:
    case TY_MATH_INT:
        return make_string_sexpr("0");

    case TY_MATH_REAL:
        return make_string_sexpr("0.0");

    case TY_RECORD:
        if (type->record_data.fields) {
            // ((instance $PROD types) default-values)
            struct Sexpr *ctor = make_string_sexpr("$PROD");
            make_instance(&ctor, verify_name_type_list(type->record_data.fields));

            struct Sexpr *result = make_list1_sexpr(ctor);
            struct Sexpr **tail = &result->right;

            for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
                *tail = make_list1_sexpr(make_default(cxt, field->type));
                tail = &(*tail)->right;
            }

            return result;
        } else {
            // just $PROD
            return make_string_sexpr("$PROD");
        }

    case TY_VARIANT:
        {
            // ((instance $IN0 types) default-of-first-type)
            struct Sexpr *ctor = make_string_sexpr("$IN0");
            make_instance(&ctor, verify_name_type_list(type->variant_data.variants));

            return make_list2_sexpr(ctor, make_default(cxt, type->variant_data.variants->type));
        }

    case TY_ARRAY:
        if (type->array_data.sizes != NULL) {
            return make_default_fixed_array(cxt, type);

        } else {
            struct Sexpr *element_type = verify_type(type->array_data.element_type);
            struct Sexpr *index_type = array_index_type(type->array_data.ndim);

            // $ARBITRARY-ARRAY is an array where all elements are equal to
            // $ARBITRARY at the element type.
            struct Sexpr *default_array = make_string_sexpr("$ARBITRARY-ARRAY");
            make_instance(&default_array,
                          make_list2_sexpr(copy_sexpr(index_type),
                                           element_type));
            element_type = NULL;

            struct Sexpr *default_size;
            if (type->array_data.ndim == 1) {
                default_size = make_string_sexpr("0");
                free_sexpr(index_type);

            } else {
                struct Sexpr *zeroes = NULL;
                struct Sexpr **tail = &zeroes;
                for (int i = 0; i < type->array_data.ndim; ++i) {
                    *tail = make_list1_sexpr(make_string_sexpr("0"));
                    tail = &(*tail)->right;
                }

                default_size = make_pair_sexpr(index_type, zeroes);
            }

            struct Sexpr *ctor = verify_type(type);
            return make_list3_sexpr(ctor, default_array, default_size);
        }

    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
    case TY_APP:
        fatal_error("invalid type for TM_DEFAULT");
    }

    fatal_error("make_default: unknown type tag");
}

static void* verify_default(void *context, struct Term *term, void *type_result)
{
    return make_default(context, term->type);
}

static void* verify_bool_literal(void *context, struct Term *term, void *type_result)
{
    if (term->bool_literal.value) {
        return make_string_sexpr("true");
    } else {
        return make_string_sexpr("false");
    }
}

static void* verify_int_literal(void *context, struct Term *term, void *type_result)
{
    // int literals are already confirmed to be in range (by typechecker)
    // so we can just convert to an s-expr
    if (term->int_literal.data[0] == '-') {
        return make_list2_sexpr(make_string_sexpr("-"),
                                make_string_sexpr(&term->int_literal.data[1]));
    } else {
        return make_string_sexpr(term->int_literal.data);
    }
}


// returns true if this string has been seen before, false if it is new
static bool get_name_for_string(struct VContext *cxt,
                                struct Term *term,
                                char **out)
{
    uint32_t length = term->string_literal.length;
    const uint8_t *data = term->string_literal.data;

    // Use (upto) the first 8 chars of the string as part of the
    // variable name, but editing out non-alphanumeric chars.
    // If this doesn't produce a unique name, add a numeric suffix.
    enum { CODENAME_LEN = 9 };
    char codename[CODENAME_LEN + 1] = "";
    codename[0] = '.';
    codename[1] = 0;
    for (uint32_t i = 0; i+1 < CODENAME_LEN && i < length; ++i) {
        if (isalnum(data[i])) {
            codename[i+1] = data[i];
        } else {
            codename[i+1] = 'x';
        }
        codename[i+2] = 0;
    }

    // make it more pretty for empty strings :)
    if (length == 0) {
        strcpy(codename, ".empty");
    }

    for (uint32_t n = 0; n < UINT32_MAX; ++n) {
        *out = copy_string_3("$String.", cxt->current_decl_name, codename);
        if (n != 0) {
            char buf[20];
            sprintf(buf, ".%" PRIu32, n);
            char *with_suffix = copy_string_2(*out, buf);
            free(*out);
            *out = with_suffix;
        }

        struct Term *prev_term = hash_table_lookup(cxt->string_names, *out);
        if (prev_term
        && prev_term->string_literal.length == length
        && memcmp(prev_term->string_literal.data, data, length) == 0) {
            // We have seen this string before.
            return true;
        }

        if (prev_term != NULL) {
            // There is a different string occupying this same hash,
            // so try the next hash value (next n)
            free(*out);
            continue;
        }

        // We have a new string
        hash_table_insert(cxt->string_names, copy_string(*out), copy_term(term));
        return false;
    }

    fatal_error("get_name_for_string failed");
}

static void* verify_string_literal(void *context, struct Term *term, void *type_result)
{
    struct VContext *cxt = context;

    // find an unused string hash code.
    char *name;
    bool seen_before = get_name_for_string(cxt, term, &name);

    if (!seen_before) {
        // fol_type is (Array Int Int)
        struct Sexpr *fol_type = verify_type(term->type);

        struct Sexpr *axioms = NULL;
        struct Sexpr **tail = &axioms;

        // for each INDEX: (assert (= (select name INDEX) CHAR))
        for (uint32_t i = 0; i < term->string_literal.length; ++i) {
            char num[40];
            sprintf(num, "%" PRIu32, i);
            struct Sexpr *index = make_string_sexpr(num);

            sprintf(num, "%" PRIu8, term->string_literal.data[i]);
            struct Sexpr *character = make_string_sexpr(num);

            struct Sexpr *axiom =
                make_list2_sexpr(
                    make_string_sexpr("assert"),
                    make_list3_sexpr(
                        make_string_sexpr("="),
                        make_list3_sexpr(
                            make_string_sexpr("select"),
                            make_string_sexpr(name),
                            index),
                        character));

            *tail = make_list1_sexpr(axiom);
            tail = &(*tail)->right;
        }

        // the result must also be a valid array
        // (e.g. elements outside the valid range must be equal to $ARBITRARY)
        struct Sexpr * validity = validity_test_expr(term->type, name);
        validity = make_list2_sexpr(make_string_sexpr("assert"), validity);
        *tail = make_list1_sexpr(validity);
        tail = &(*tail)->right;

        // make an Item for the string literal
        struct Item *item = alloc(sizeof(struct Item));
        memset(item, 0, sizeof(struct Item));

        item->fol_decl = make_list3_sexpr(
            make_string_sexpr("declare-const"),
            make_string_sexpr(name),
            copy_sexpr(fol_type));

        item->fol_axioms = axioms;

        item->fol_name = copy_string(name);
        item->fol_type = fol_type;

        hash_table_insert(cxt->global_env, copy_string(name), item);
    }

    // return the result
    return make_string_sexpr_handover(name);
}

static void* verify_array_literal(void *context, struct Term *term, void *type_result, void *list_result)
{
    struct VContext *cxt = context;
    struct Sexpr *sub_exprs = list_result;

    const char *key = "$ArrayLiteralNum";
    void *value = hash_table_lookup(cxt->string_names, key);
    uintptr_t unique_num = (uintptr_t)value;
    hash_table_insert(cxt->string_names, key, (void*)(unique_num + 1));

    char name[60];
    sprintf(name, "$ArrLit.%s.%" PRIuPTR, cxt->current_decl_name, unique_num);

    // fol_type is (Array Int ElemType)
    struct Sexpr *fol_type = verify_type(term->type);

    struct Sexpr *axioms = NULL;
    struct Sexpr **tail = &axioms;

    uint64_t index = 0;
    while (sub_exprs) {
        char num[50];
        sprintf(num, "%" PRIu64, index++);
        struct Sexpr *index_expr = make_string_sexpr(num);

        struct Sexpr *axiom =
            make_list2_sexpr(
                make_string_sexpr("assert"),
                make_list3_sexpr(
                    make_string_sexpr("="),
                    make_list3_sexpr(
                        make_string_sexpr("select"),
                        make_string_sexpr(name),
                        index_expr),
                    sub_exprs->left));
        sub_exprs->left = NULL;

        struct Sexpr *next = sub_exprs->right;
        sub_exprs->right = NULL;

        free_sexpr(sub_exprs);
        sub_exprs = next;

        *tail = make_list1_sexpr(axiom);
        tail = &(*tail)->right;
    }

    // the result must also be a valid array
    // (e.g. elements outside the valid range must be equal to $ARBITRARY)
    struct Sexpr * validity = validity_test_expr(term->type, name);
    validity = make_list2_sexpr(make_string_sexpr("assert"), validity);
    *tail = make_list1_sexpr(validity);
    tail = &(*tail)->right;

    // make an Item for the array literal
    struct Item *item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));

    item->fol_decl = make_list3_sexpr(
        make_string_sexpr("declare-const"),
        make_string_sexpr(name),
        copy_sexpr(fol_type));

    item->fol_axioms = axioms;

    item->fol_name = copy_string(name);
    item->fol_type = fol_type;

    hash_table_insert(cxt->global_env, copy_string(name), item);

    // return the result
    return make_string_sexpr(name);
}

static struct Sexpr* verify_numeric_cast(struct VContext *cxt, struct Term *term, struct Sexpr *operand)
{
    enum TypeTag from_tag = term->cast.operand->type->tag;
    enum TypeTag to_tag = term->type->tag;

    bool from_signed = false;
    int from_num_bits = 0;
    bool to_signed = false;
    int to_num_bits = 0;

    if (from_tag == TY_FINITE_INT) {
        from_signed = term->cast.operand->type->int_data.is_signed;
        from_num_bits = term->cast.operand->type->int_data.num_bits;
    }
    if (to_tag == TY_FINITE_INT) {
        to_signed = term->type->int_data.is_signed;
        to_num_bits = term->type->int_data.num_bits;
    }

    // Insert "to_real" or "to_int" if required
    // (Note: casting from real to int doesn't check if the number is an integer;
    // instead it does a "floor" operation.)
    if (from_tag == TY_MATH_REAL) {
        if (to_tag != TY_MATH_REAL) {
            operand = make_list2_sexpr(make_string_sexpr("to_int"),
                                       operand);
        }
    } else if (to_tag == TY_MATH_REAL) {
        operand = make_list2_sexpr(make_string_sexpr("to_real"),
                                   operand);
    }

    // A check is needed if:
    //  - going from signed to unsigned, at any width
    //      (e.g. -1 cannot be represented as unsigned)
    //  - going from unsigned to signed -- unless widening
    //      (e.g. 65535 as u16 is not representable in i16 or i8, but is representable in i32 or i64)
    //  - not changing signedness -- when narrowing
    //      (e.g. 20000 as i16 is representable in i16,i32,i64 but not i8)

    bool need_check = false;
    if (to_num_bits != 0) {
        if (from_num_bits == 0) {
            need_check = true;
        } else if (from_signed && !to_signed) {
            need_check = true;
        } else if (!from_signed && to_signed) {
            need_check = (to_num_bits <= from_num_bits);
        } else {
            need_check = (to_num_bits < from_num_bits);
        }
    }

    if (need_check) {
        char *check_fun = copy_string_2("$in_range_", int_type_string(term->type));
        struct Sexpr * condition_expr =
            make_list2_sexpr(make_string_sexpr_handover(check_fun),
                             copy_sexpr(operand));

        verify_condition(cxt, term->location, condition_expr, "cast",
                         err_msg_operator_precondition_fail(term));
        free_sexpr(condition_expr);
    }

    return operand;
}

static struct Sexpr *verify_array_cast(struct VContext *cxt, struct Term *term, struct Sexpr *operand)
{
    if (term->type->array_data.sizes != NULL) {
        if (term->cast.operand->type->array_data.sizes != NULL) {
            return operand;
        } else {
            // Cast of T[*] or T[] to T[n].

            // Verify that the array does have size n.
            struct Sexpr *expected_size = fixed_arr_size_sexpr(term->type);
            struct Sexpr *cond =
                match_arr_size(
                    "$arr", "$size",
                    copy_sexpr(operand), term->cast.operand->type,
                    make_list3_sexpr(
                        make_string_sexpr("="),
                        expected_size,   // handover
                        make_string_sexpr("$size")));
            expected_size = NULL;
            verify_condition(cxt, term->location, cond, "array size", err_msg_array_wrong_size(term));
            free_sexpr(cond);

            // Just extract the Array (first field of array-tuple).
            return match_arr_size(
                "$arr", "$size",
                operand, // handover
                term->cast.operand->type,
                make_string_sexpr("$arr"));
        }
    } else {
        if (term->cast.operand->type->array_data.sizes == NULL) {
            return operand;
        } else {
            // Cast of T[n] to T[].

            // ctor = (instance $PROD (arraytype indextype))
            struct Sexpr *ctor = verify_type(term->type);

            // return (ctor operand size)
            return make_list3_sexpr(ctor,
                                    operand,
                                    fixed_arr_size_sexpr(term->cast.operand->type));
        }
    }
}

static void* verify_cast(void *context, struct Term *term, void *type_result, void *target_type_result, void *operand_result)
{
    if (term->type->tag == TY_ARRAY) {
        return verify_array_cast(context, term, operand_result);
    } else {
        return verify_numeric_cast(context, term, operand_result);
    }
}

static void* nr_verify_if(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct VContext *cxt = context;

    struct Sexpr *cond = transform_term(tr, context, term->if_data.cond);

    // assume cond is true on the "then" branch
    struct Sexpr *old_pc = copy_sexpr(cxt->path_condition);
    cxt->path_condition = and_sexpr(cxt->path_condition, copy_sexpr(cond));

    struct Sexpr * then_expr = transform_term(tr, context, term->if_data.then_branch);

    // assume cond is false on the "else" branch
    free_sexpr(cxt->path_condition);
    cxt->path_condition = and_not_sexpr(copy_sexpr(old_pc), copy_sexpr(cond));

    struct Sexpr * else_expr = transform_term(tr, context, term->if_data.else_branch);

    free_sexpr(cxt->path_condition);
    cxt->path_condition = old_pc;

    return make_list4_sexpr(make_string_sexpr("ite"), cond, then_expr, else_expr);
}

static void* verify_unop(void *context, struct Term *term, void *type_result, void *operand_result)
{
    struct VContext *cxt = context;

    struct Sexpr *operand = operand_result;

    // Check Operator Preconditions
    char *check_fun = NULL;

    switch (term->unop.operator) {
    case UNOP_NEGATE:
        if (term->unop.operand->type->tag == TY_FINITE_INT) {
            check_fun = copy_string_2("$can_neg_", int_type_string(term->unop.operand->type));
        }
        break;

    case UNOP_COMPLEMENT:
    case UNOP_NOT:
        // No preconditions
        break;
    }

    if (check_fun != NULL) {
        // (check_fun operand)
        struct Sexpr * condition_expr =
            make_list2_sexpr(make_string_sexpr_handover(check_fun),
                             copy_sexpr(operand));

        verify_condition(cxt, term->location, condition_expr, "unary operator",
                         err_msg_operator_precondition_fail(term));
        free_sexpr(condition_expr);
    }

    // Convert to Sexpr
    struct Sexpr *result = NULL;
    switch (term->unop.operator) {
    case UNOP_NEGATE:
        result = make_list2_sexpr(make_string_sexpr("-"), operand);
        break;

    case UNOP_COMPLEMENT:
        // ($cpl_i8 operand)
        result = make_list2_sexpr(
            make_string_sexpr_handover(copy_string_2("$cpl_", int_type_string(term->unop.operand->type))),
            operand);
        break;

    case UNOP_NOT:
        result = make_list2_sexpr(make_string_sexpr("not"), operand);
        break;
    }
    return result;
}

static void* nr_verify_binop(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct VContext *cxt = context;

    // Transform/verify the LHS
    struct Sexpr *lhs = transform_term(tr, context, term->binop.lhs);

    // Transform/verify the RHS
    struct Sexpr *rhs;
    enum BinOp binop = term->binop.list->operator;

    if (binop == BINOP_AND || binop == BINOP_OR || binop == BINOP_IMPLIES) {
        // In A && B and A ==> B, when verifying B, we may assume A.
        // In A || B, we may assume !A instead.
        struct Sexpr *old_pc = copy_sexpr(cxt->path_condition);

        struct Sexpr *new_cond = copy_sexpr(lhs);
        if (binop == BINOP_OR) {
            cxt->path_condition = and_not_sexpr(cxt->path_condition, new_cond);
        } else {
            cxt->path_condition = and_sexpr(cxt->path_condition, new_cond);
        }
        new_cond = NULL;

        rhs = transform_term(tr, context, term->binop.list->rhs);

        free_sexpr(cxt->path_condition);
        cxt->path_condition = old_pc;

    } else {
        rhs = transform_term(tr, context, term->binop.list->rhs);
    }

    // "ty" string needed for some integer operations
    const char *ty = term->binop.lhs->type->tag == TY_FINITE_INT ? int_type_string(term->binop.lhs->type) : "";

    // Verify Operator Preconditions
    // (most of these apply to TY_FINITE_INT only, although BINOP_DIVIDE and BINOP_MODULO
    // also have preconditions for TY_MATH_INT.)
    char *check_fun = NULL;

    if (term->type->tag == TY_FINITE_INT) {
        switch (binop) {
        case BINOP_PLUS:
            check_fun = copy_string_2("$can_add_", ty);
            break;

        case BINOP_MINUS:
            check_fun = copy_string_2("$can_sub_", ty);
            break;

        case BINOP_TIMES:
            check_fun = copy_string_2("$can_mul_", ty);
            break;

        case BINOP_DIVIDE:
        case BINOP_MODULO:
            check_fun = copy_string_2("$can_div_", ty);
            break;

        case BINOP_BITAND:
        case BINOP_BITOR:
        case BINOP_BITXOR:
            // no precondition
            break;

        case BINOP_SHIFTLEFT:
            check_fun = copy_string_2("$can_shl_", ty);
            break;

        case BINOP_SHIFTRIGHT:
            check_fun = copy_string_2("$can_shr_", ty);
            break;

        case BINOP_EQUAL:
        case BINOP_NOT_EQUAL:
        case BINOP_LESS:
        case BINOP_LESS_EQUAL:
        case BINOP_GREATER:
        case BINOP_GREATER_EQUAL:
        case BINOP_AND:
        case BINOP_OR:
        case BINOP_IMPLIES:
        case BINOP_IFF:
            // no precondition
            break;

        case BINOP_IMPLIED_BY:
            fatal_error("<== should have been removed by typechecker");
        }
    }

    struct Sexpr *condition_expr = NULL;
    if (check_fun) {
        // (check_fun lhs rhs)
        condition_expr =
            make_list3_sexpr(make_string_sexpr_handover(check_fun),
                             copy_sexpr(lhs),
                             copy_sexpr(rhs));
    } else if (binop == BINOP_DIVIDE || binop == BINOP_MODULO) {
        condition_expr =
            make_list3_sexpr(make_string_sexpr("distinct"),
                             copy_sexpr(rhs),
                             make_string_sexpr(term->type->tag == TY_MATH_REAL ? "0.0" : "0"));
    }

    if (condition_expr) {
        verify_condition(cxt, term->location, condition_expr, "binary operator",
                         err_msg_operator_precondition_fail(term));
        free_sexpr(condition_expr);
    }

    // Convert to Sexpr
    struct Sexpr *op = NULL;
    switch (binop) {
    case BINOP_PLUS:
        op = make_string_sexpr("+");
        break;

    case BINOP_MINUS:
        op = make_string_sexpr("-");
        break;

    case BINOP_TIMES:
        op = make_string_sexpr("*");
        break;

    case BINOP_DIVIDE:
        if (term->type->tag == TY_MATH_REAL) {
            op = make_string_sexpr("/");
        } else if (term->type->tag == TY_MATH_INT) {
            op = make_string_sexpr("$div_int");
        } else if (ty[0] == 'i') {
            op = make_string_sexpr_handover(copy_string_2("$div_", ty));
        } else {
            op = make_string_sexpr("div");
        }
        break;

    case BINOP_MODULO:
        if (term->type->tag == TY_MATH_INT) {
            op = make_string_sexpr("$mod_int");
        } else if (ty[0] == 'i') {
            op = make_string_sexpr_handover(copy_string_2("$mod_", ty));
        } else {
            op = make_string_sexpr("mod");
        }
        break;

    case BINOP_BITAND:
        op = make_string_sexpr_handover(copy_string_2("$and_", ty));
        break;

    case BINOP_BITOR:
        op = make_string_sexpr_handover(copy_string_2("$or_", ty));
        break;

    case BINOP_BITXOR:
        op = make_string_sexpr_handover(copy_string_2("$xor_", ty));
        break;

    case BINOP_SHIFTLEFT:
        op = make_string_sexpr_handover(copy_string_2("$shl_", ty));
        break;

    case BINOP_SHIFTRIGHT:
        op = make_string_sexpr_handover(copy_string_2("$shr_", ty));
        break;

    case BINOP_EQUAL:
    case BINOP_IFF:
        op = make_string_sexpr("=");
        break;

    case BINOP_NOT_EQUAL:
        op = make_string_sexpr("distinct");
        break;

    case BINOP_LESS:
        op = make_string_sexpr("<");
        break;

    case BINOP_LESS_EQUAL:
        op = make_string_sexpr("<=");
        break;

    case BINOP_GREATER:
        op = make_string_sexpr(">");
        break;

    case BINOP_GREATER_EQUAL:
        op = make_string_sexpr(">=");
        break;

    case BINOP_AND:
        op = make_string_sexpr("and");
        break;

    case BINOP_OR:
        op = make_string_sexpr("or");
        break;

    case BINOP_IMPLIES:
        op = make_string_sexpr("=>");
        break;

    case BINOP_IMPLIED_BY:
        fatal_error("<== should have been removed by typechecker");
        break;
    }
    if (op == NULL) {
        fatal_error("verify_binop unknown operator");
    }

    // (op lhs rhs)
    return make_list3_sexpr(op, lhs, rhs);
}

static void* nr_verify_let(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct VContext *cxt = context;

    // Transform/verify RHS
    struct Sexpr *rhs = transform_term(tr, context, term->let.rhs);

    // (Temporarily) add the new variable into the verifier env.
    struct Item *item = update_local(cxt,
                                     term->let.name,
                                     NULL,
                                     verify_type(term->let.rhs->type),
                                     copy_sexpr(rhs));

    // Transform/verify body
    struct Sexpr *body = transform_term(tr, context, term->let.body);

    const char *fol_name = NULL;

    // Remove the temporary definition, as we will be changing it into a "let", so
    // we won't need a separate definition in the env any more
    fol_name = item->fol_name;
    item->fol_name = NULL;
    remove_existing_item(cxt->local_env, fol_name);

    // Any facts mentioning the let-bound variable are now (unfortunately)
    // invalid. Rather than trying to make them valid, we just remove them.
    remove_facts(cxt, fol_name);

    // Produce the final "let" sexpr
    return make_list3_sexpr(
        make_string_sexpr("let"),
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr_handover(fol_name),
                rhs)),
        body);
}

static void* nr_verify_quantifier(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct VContext *cxt = context;

    // (Temporarily) add the new variable into the verifier env
    struct Sexpr *fol_type = verify_type(term->quant.type);

    struct Item *item = update_local(cxt,
                                     term->quant.name,
                                     term->quant.type,
                                     copy_sexpr(fol_type),
                                     NULL);

    // Transform/verify body
    struct Sexpr *body = transform_term(tr, context, term->quant.body);

    // Remove the temporary definition, as we will be changing it into a "forall" or "exists",
    // so we won't need a separate definition in the env any more
    const char *fol_name = item->fol_name;
    item->fol_name = NULL;
    remove_existing_item(cxt->local_env, fol_name);

    // Any facts mentioning the quantified variable are now (unfortunately) invalid. Rather
    // than trying to make them valid, we just remove them.
    remove_facts(cxt, fol_name);

    // Produce the final "forall" or "exists" sexpr
    const char *qname = NULL;
    switch (term->quant.quant) {
    case QUANT_FORALL: qname = "forall"; break;
    case QUANT_EXISTS: qname = "exists"; break;
    }

    struct Sexpr *varlist =
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr_handover(fol_name),
                fol_type));

    body = insert_validity_condition(cxt, term->quant.quant, term->quant.type, varlist->left->left, body);

    return make_list3_sexpr(make_string_sexpr(qname), varlist, body);
}

// copies (the relevant parts of) all sexpr inputs
struct Sexpr * add_funarg_lets(struct Item *item, struct Sexpr *cond,
                               struct Sexpr *generic_arg_list, struct Sexpr *arglist)
{
    // Substitute the type variables
    struct Sexpr *cond2 = substitute_in_sexpr(item->fol_generic_vars, generic_arg_list, cond);

    // Insert a let to account for the term arguments
    struct Sexpr *dummies = item->fol_dummies;
    struct Sexpr *lets = NULL;

    while (dummies) {
        lets = make_pair_sexpr(
                    make_list2_sexpr(
                        copy_sexpr(dummies->left),
                        copy_sexpr(arglist->left)),
                    lets);
        dummies = dummies->right;
        arglist = arglist->right;
    }

    if (lets == NULL) {
        return cond2;
    } else {
        return make_list3_sexpr(make_string_sexpr("let"),
                                lets,
                                cond2);
    }
}

// helper for handle_ref_args
static struct Sexpr * expanded_fol_ret_type(struct TypeData_Function *func_data)
{
    struct Type *expanded_ret_ty = get_expanded_ret_type(func_data->args, func_data->return_type);
    struct Sexpr *fol_ret_ty = verify_type(expanded_ret_ty);
    free_type(expanded_ret_ty);
    return fol_ret_ty;
}

// "call_expr" is handed over
static struct Sexpr * handle_ref_args(struct VContext *cxt,
                                      struct Term *term,
                                      struct Sexpr *call_expr)
{
    bool ref_found = false;

    if (term->tag != TM_CALL || term->call.func->type->tag != TY_FUNCTION) {
        fatal_error("call not in expected form");
    }

    struct Sexpr *fol_ret_ty = expanded_fol_ret_type(&term->call.func->type->function_data);

    struct FunArg *formal = term->call.func->type->function_data.args;
    struct OpTermList *actual = term->call.args;
    int num = 1;
    while (formal) {
        if (formal->ref) {
            // make a term like ($FLD3 (f arg1 arg2))
            struct Sexpr *projection = make_list2_sexpr(
                ret_fldn(num, fol_ret_ty),
                copy_sexpr(call_expr));

            // assign that term to the reference
            struct RefChain *ref = ref_chain_for_term(cxt, actual->rhs);
            update_reference(cxt, ref, projection);
            projection = NULL;
            free_ref_chain(ref);

            ref_found = true;
            ++num;
        }

        formal = formal->next;
        actual = actual->next;
    }

    // turn call_expr into ($FLD0 (f args)) if required
    if (ref_found) {
        call_expr = make_list2_sexpr(ret_fldn(0, fol_ret_ty), call_expr);
    }

    free_sexpr(fol_ret_ty);
    return call_expr;
}


// Aliasing checks

struct RefArgInfo {
    int arg_num;
    bool ref;
    struct Location *location;
    struct RefChain *ref_chain;  // reversed, and casts removed
    struct RefArgInfo *next;
};

static struct RefChain * reverse_ref_chain_and_remove_casts(struct RefChain *r)
{
    struct RefChain *prev = NULL;
    struct RefChain *curr = r;
    while (curr) {
        struct RefChain *next = curr->base;

        // array casts are irrelevant for aliasing detection; remove them
        if (curr->ref_type == RT_ARRAY_CAST) {
            curr->base = NULL;
            free_ref_chain(curr);
            curr = next;

        } else {
            curr->base = prev;
            prev = curr;
            curr = next;
        }
    }
    return prev;
}

static struct RefArgInfo * get_ref_arg_info(struct VContext *cxt,
                                            int arg_num,
                                            struct FunArg *formal,
                                            struct OpTermList *actual)
{
    if (formal == NULL) {
        return NULL;
    }

    struct RefArgInfo *next = get_ref_arg_info(cxt, arg_num + 1, formal->next, actual->next);

    struct RefArgInfo *info = alloc(sizeof(struct RefArgInfo));
    info->arg_num = arg_num;
    info->ref = formal->ref;
    info->location = &actual->rhs->location;
    if (ref_chain_is_lvalue(actual->rhs)) {
        info->ref_chain = reverse_ref_chain_and_remove_casts(ref_chain_for_term(cxt, actual->rhs));
    } else {
        info->ref_chain = NULL;
    }
    info->next = next;
    return info;
}

// returns false if cannot alias, true if may alias and
// equality_conditions need to be checked.
static bool alias_check(struct RefChain *r1,
                        struct RefChain *r2,
                        struct Sexpr **equality_conditions)
{
    if (r1->base && r2->base) {
        if (alias_check(r1->base, r2->base, equality_conditions) == false) {
            // aliasing ruled out
            return false;
        }
    }

    if (r1->ref_type != r2->ref_type) {
        // e.g. RT_LOCAL_VAR vs. RT_SEXPR can happen.
        // In this case the terms cannot alias.
        return false;
    }

    switch (r1->ref_type) {
    case RT_LOCAL_VAR:
        // may-alias if variable names are the same
        return (strcmp(r1->variable_name, r2->variable_name) == 0);

    case RT_FIELD:
    case RT_VARIANT:
        // may-alias if field/variant are the same
        return r1->index == r2->index;

    case RT_ARRAY_ELEMENT:
        // may-alias, need to check if array indexes are the same
        ;
        struct Sexpr *eq_expr = make_list3_sexpr(make_string_sexpr("="),
                                                 copy_sexpr(r1->array_index),
                                                 copy_sexpr(r2->array_index));
        *equality_conditions = make_pair_sexpr(eq_expr, *equality_conditions);
        return true;

    case RT_ARRAY_CAST:
        fatal_error("RT_ARRAY_CAST should have been removed before now");

    case RT_SEXPR:
        return false;
    }

    fatal_error("unknown ref_type");
}

static void verify_aliasing_for_args(struct VContext *cxt,
                                     struct RefArgInfo *arg1,
                                     struct RefArgInfo *arg2)
{
    struct RefChain *r1 = arg1->ref_chain;
    struct RefChain *r2 = arg2->ref_chain;

    if (r1 && r2) {
        struct Sexpr *equality_conditions = NULL;
        bool may_alias = alias_check(arg1->ref_chain, arg2->ref_chain, &equality_conditions);

        if (may_alias) {
            if (equality_conditions == NULL) {
                // There is definitely aliasing. Report error (at proper place in the output).
                char * msg = err_msg_aliasing_violation(*arg2->location, arg2->arg_num, arg1->arg_num);
                add_fol_message(msg, true, 0, NULL);

            } else {
                equality_conditions = make_list2_sexpr(make_string_sexpr("not"),
                                                       conjunction(equality_conditions));
                verify_condition(cxt, *arg2->location, equality_conditions, "aliasing",
                                 err_msg_possible_aliasing_violation(*arg2->location,
                                                                     arg2->arg_num,
                                                                     arg1->arg_num));
            }
        }

        free_sexpr(equality_conditions);
    }
}

static void verify_aliasing(struct VContext *cxt, struct Term *term)
{
    // NOTE: Aliasing must be checked even for ghost calls

    // Consider all arguments
    struct RefArgInfo *info = get_ref_arg_info(cxt, 1, term->call.func->type->function_data.args, term->call.args);

    // Loop through each pair of arguments, for which at least one in
    // the pair is a ref.
    for (struct RefArgInfo *arg1 = info; arg1; arg1 = arg1->next) {
        for (struct RefArgInfo *arg2 = info; arg2 != arg1; arg2 = arg2->next) {
            if (arg1->ref || arg2->ref) {
                verify_aliasing_for_args(cxt, arg1, arg2);
            }
        }
    }

    // Clean up
    while (info) {
        free_ref_chain(info->ref_chain);
        struct RefArgInfo *next = info->next;
        free(info);
        info = next;
    }
}

// Given a list of type args to a function, make the "generic args" that
// must be passed to the function in the FOL representation.
// Each type arg expands into 4 sexpr args:
//  - the type itself
//  - a default value of the type
//  - a "$lambda" expression representing the "allocated" function for that type
//    (note lambdas are expanded out by substitute_in_sexpr so they do not reach the
//    SMT solver itself).
//  - a "$lambda" representing the "valid" function for that type.
static struct Sexpr * make_generic_args(struct VContext *cxt, struct TypeList *types)
{
    struct Sexpr *list = NULL;
    struct Sexpr **tail = &list;
    while (types) {
        // the type
        struct Sexpr *ty = verify_type(types->type);
        *tail = make_list1_sexpr(ty);
        tail = &((*tail)->right);

        // default value
        struct Sexpr *dflt = make_default(cxt, types->type);
        *tail = make_list1_sexpr(dflt);
        tail = &((*tail)->right);

        // allocated function
        struct Sexpr *lam = allocated_test_expr(types->type, "$x");
        if (lam == NULL) {
            lam = make_string_sexpr("false");
        }
        lam = make_list3_sexpr(make_string_sexpr("$lambda"),
                               make_list1_sexpr(make_string_sexpr("$x")),
                               lam);
        *tail = make_list1_sexpr(lam);
        tail = &((*tail)->right);

        // validity function
        lam = validity_test_expr(types->type, "$x");
        if (lam == NULL) {
            lam = make_string_sexpr("true");
        }
        lam = make_list3_sexpr(make_string_sexpr("$lambda"),
                               make_list1_sexpr(make_string_sexpr("$x")),
                               lam);
        *tail = make_list1_sexpr(lam);
        tail = &((*tail)->right);

        types = types->next;
    }
    return list;
}

struct Sexpr * verify_call_term(struct VContext *cxt,
                                struct Term *term)
{
    // Examine the function (and any type arguments)
    const char *func_src_code_name = NULL;  // shared with AST
    struct Sexpr *generic_args = NULL;      // owned

    if (term->call.func->tag == TM_VAR) {
        func_src_code_name = term->call.func->var.name;

    } else if (term->call.func->tag == TM_TYAPP) {
        if (term->call.func->tyapp.lhs->tag != TM_VAR) {
            fatal_error("function not in expected form");
        }
        func_src_code_name = term->call.func->tyapp.lhs->var.name;
        generic_args = make_generic_args(cxt, term->call.func->tyapp.tyargs);

    } else {
        fatal_error("Function not in expected form");
    }

    const char *func_fol_name = copy_string_2("%", func_src_code_name);

    // Translate the arguments
    struct Sexpr *args = NULL;
    struct Sexpr **arg_tail = &args;
    for (struct OpTermList *arg = term->call.args; arg; arg = arg->next) {
        struct Sexpr *sexpr = verify_term(cxt, arg->rhs);
        *arg_tail = make_list1_sexpr(sexpr);
        arg_tail = &(*arg_tail)->right;
    }

    // Look up preconditions
    struct Item *item = hash_table_lookup(cxt->global_env, func_fol_name);
    if (item == NULL) {
        fatal_error("Could not find function in env");
    }

    // Verify each precondition, adding a "let" expression in front
    // for the term arguments, and doing a substitution for the type
    // arguments.
    struct Condition *preconds = item->preconds;
    while (preconds) {
        struct Sexpr *cond_expr = add_funarg_lets(item, preconds->expr, generic_args, args);

        char buf1[500], buf2[520];
        format_location(&preconds->location, true, false, buf1, sizeof(buf1));
        snprintf(buf2, sizeof(buf2), "precondition at %s", buf1);

        verify_condition(cxt, term->location, cond_expr, buf2,
                         err_msg_function_precondition_fail(term, preconds->location));
        free_sexpr(cond_expr);

        preconds = preconds->next;
    }

    // Check aliasing rules
    verify_aliasing(cxt, term);

    // Make the call-expr
    struct Sexpr *call_expr;            // (f *actual-arguments*)
    struct Sexpr *call_expr_dummies;    // (f *dummy-arguments*)

    if (item->fol_decl == NULL) {
        // Impure function, doesn't have a decl. Make a new variable for the result.
        // Subtle point: we cannot use %Module.funcname as the variable name, as that would conflict
        // with the function name itself. Instead make sure we are using %Module.funcname.1 or higher.
        ensure_nonzero_name(cxt, func_src_code_name);
        struct Item *fn_item = update_local(cxt, func_src_code_name, term->type, verify_type(term->type), NULL);
        call_expr = make_string_sexpr(fn_item->fol_name);
        call_expr_dummies = make_string_sexpr(fn_item->fol_name);

    } else {
        // Normal function call

        call_expr = make_string_sexpr(func_fol_name);
        call_expr_dummies = make_string_sexpr(func_fol_name);

        // add the generic_args, if any
        if (generic_args) {
            make_instance(&call_expr, copy_sexpr(generic_args));
            make_instance(&call_expr_dummies, copy_sexpr(item->fol_generic_vars));
        }

        // add the args, if any
        if (args != NULL) {
            call_expr = make_pair_sexpr(call_expr, copy_sexpr(args));
            call_expr_dummies = make_pair_sexpr(call_expr_dummies, copy_sexpr(item->fol_dummies));
        }
    }

    // Add postconditions to the known facts.
    struct Condition *postconds = item->postconds;
    while (postconds) {
        struct Sexpr *cond_expr = add_return_if_required(
            copy_sexpr(call_expr_dummies),
            copy_sexpr(postconds->expr));

        struct Sexpr *expr2 = add_funarg_lets(item, cond_expr, generic_args, args);
        free_sexpr(cond_expr);
        add_fact(cxt, expr2);

        postconds = postconds->next;
    }

    free_sexpr(call_expr_dummies);
    call_expr_dummies = NULL;

    // Handle any "refs"
    call_expr = handle_ref_args(cxt, term, call_expr);

    free_sexpr(generic_args);
    free_sexpr(args);
    free((char*)func_fol_name);

    return call_expr;
}

static void * nr_verify_call(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    return verify_call_term(context, term);
}

static void * verify_record(void *context, struct Term *term, void *type_result, void *fields_result)
{
    struct Sexpr * types = verify_name_type_list(term->type->record_data.fields);

    struct Sexpr * ctor = make_string_sexpr("$PROD");
    make_instance(&ctor, types);
    types = NULL;

    if (fields_result) {
        return make_pair_sexpr(ctor, fields_result);
    } else {
        return ctor;
    }
}

static void * verify_record_update(void *context, struct Term *term, void *type_result, void *lhs_result, void *fields_result)
{
    struct VContext *cxt = context;

    // lhs_type will be of form (instance $PROD types)
    struct Sexpr *lhs_type = verify_type(term->record_update.lhs->type);
    struct Sexpr *field_types = lhs_type->right->right->left;

    struct Sexpr *lhs = lhs_result;
    if (lhs->type != S_STRING) {
        uintptr_t unique_num = (uintptr_t) hash_table_lookup(cxt->local_counter, "$RecordUpdate");
        hash_table_insert(cxt->local_counter, "$RecordUpdate", (void*)(unique_num + 1));
        char unique_suffix[60];
        sprintf(unique_suffix, "%" PRIuPTR, unique_num);

        const char *lhs_name = copy_string_2("$RecordUpdate.", unique_suffix);
        add_const_item(context,
                       copy_string(lhs_name),
                       NULL,
                       copy_sexpr(lhs_type),
                       lhs,   // handover
                       true);
        lhs = make_string_sexpr_handover(lhs_name);
    }

    struct Sexpr *new_lhs = copy_record_fields(lhs, field_types);
    free_sexpr(lhs);

    free_sexpr(lhs_type);
    lhs_type = NULL;
    field_types = NULL;

    // now replace all the updated fields
    struct NameTermList *update = term->record_update.fields;
    struct Sexpr *new_term_node = fields_result;
    while (update) {
        // locate the field
        struct Sexpr *new_lhs_node = new_lhs->right;
        struct NameTypeList *type_node = term->type->record_data.fields;
        while (strcmp(update->name, type_node->name) != 0) {
            new_lhs_node = new_lhs_node->right;
            type_node = type_node->next;
        }
        free_sexpr(new_lhs_node->left);
        new_lhs_node->left = new_term_node->left;
        new_term_node->left = NULL;
        update = update->next;
        new_term_node = new_term_node->right;
    }

    free_sexpr(fields_result);

    return new_lhs;
}

static void * verify_field_proj(void *context, struct Term *term, void *type_result, void *lhs_result)
{
    // find which field number we are looking at
    int num = 0;
    for (struct NameTypeList *field = term->field_proj.lhs->type->record_data.fields; field; field = field->next) {
        if (strcmp(field->name, term->field_proj.field_name) == 0) {
            break;
        }
        ++num;
    }

    char buf[30];
    sprintf(buf, "$FLD%d", num);
    struct Sexpr *selector = make_string_sexpr(buf);

    struct Sexpr *types = verify_name_type_list(term->field_proj.lhs->type->record_data.fields);
    make_instance(&selector, types);

    return make_list2_sexpr(selector, lhs_result);
}

static void * verify_variant(void *context, struct Term *term, void *type_result, void *payload_result)
{
    // find which variant we are looking at
    int num = 0;
    for (struct NameTypeList *variant = term->type->variant_data.variants; variant; variant = variant->next) {
        if (strcmp(variant->name, term->variant.variant_name) == 0) {
            break;
        }
        ++num;
    }

    char buf[30];
    sprintf(buf, "$IN%d", num);
    struct Sexpr * ctor = make_string_sexpr(buf);

    struct Sexpr * types = verify_name_type_list(term->type->variant_data.variants);
    make_instance(&ctor, types);

    return make_list2_sexpr(ctor, payload_result);
}

static void * nr_verify_match(struct TermTransform *tr, void *context, struct Term *term, void *type_result)
{
    struct VContext *cxt = context;

    struct Sexpr *scrut_result = transform_term(tr, context, term->match.scrutinee);

    struct Type *variant_type = term->match.scrutinee->type;

    struct Sexpr *backup_path_condition = cxt->path_condition;
    cxt->path_condition = NULL;

    struct Sexpr *arm_exprs = NULL;
    struct Sexpr **arm_tail = &arm_exprs;

    struct Sexpr *check_exprs = NULL;
    struct Sexpr **check_tail = &check_exprs;

    uint64_t wildcard_counter = 0;

    for (struct Arm *arm = term->match.arms; arm; arm = arm->next) {
        if (arm->pattern->tag == PAT_VARIANT) {

            // Find some information about the chosen variant
            struct Type *payload_type;
            struct Sexpr *ctor;
            struct Sexpr *tester;
            struct Sexpr *selector;
            analyse_variant(arm->pattern->variant.variant_name,
                            variant_type,
                            &payload_type,
                            &ctor,
                            &tester,
                            &selector);

            // build a "check expression" that checks that the scrutinee matches this variant
            struct Sexpr *check_expr =
                make_list2_sexpr(tester, copy_sexpr(scrut_result));
            *check_tail = make_list1_sexpr(check_expr);
            check_tail = &(*check_tail)->right;

            // a new Item for the payload-variable, if there is one
            struct Item *item = NULL;

            if (arm->pattern->variant.payload->tag == PAT_VAR) {
                // build an expr to extract the payload
                struct Sexpr *payload_expr =
                    make_list2_sexpr(selector, copy_sexpr(scrut_result));

                // Temporarily add a new variable into the environment
                item = update_local(cxt,
                                    arm->pattern->variant.payload->var.name,
                                    NULL,
                                    verify_type(payload_type),
                                    payload_expr);  // handover
            } else {
                free_sexpr(selector);
            }

            // assume the check_expr is true
            cxt->path_condition = and_sexpr(copy_sexpr(backup_path_condition),
                                            copy_sexpr(check_expr));

            // Verify the rhs
            struct Sexpr *rhs_expr = transform_term(tr, context, arm->rhs);

            // Undo the change to the path condition
            free_sexpr(cxt->path_condition);
            cxt->path_condition = NULL;

            // Remove the temporary definition
            const char *fol_name = NULL;
            if (item) {
                fol_name = item->fol_name;
                item->fol_name = NULL;
                remove_existing_item(cxt->local_env, fol_name);
                remove_facts(cxt, fol_name);
            } else {
                // It's a wildcard pattern...

                // Note: it's not valid to use "_" as a wildcard
                // pattern because "_" is reserved in SMT-LIB for
                // indexed identifiers. Instead we just use a dummy
                // variable name.

                // Also: CVC5 seems to complain if two different arms
                // of a match use the same "$wild" name, e.g.
                // (match x ( ((CTOR $wild) rhs1) ($wild rhs2) ))
                // seems to be rejected. AFAIK this is legal in SMT-LIB,
                // but for the benefit of CVC5 we can generate different
                // names ($wild0 and $wild1) here.

                char buf[50];
                sprintf(buf, "$wild%" PRIu64, wildcard_counter);
                wildcard_counter++;

                fol_name = copy_string(buf);
            }

            // Create a sexpr for this arm
            struct Sexpr *arm_expr =
                make_list2_sexpr(
                    make_list2_sexpr(
                        ctor,
                        make_string_sexpr_handover(fol_name)),
                    rhs_expr);
            *arm_tail = make_list1_sexpr(arm_expr);
            arm_tail = &(*arm_tail)->right;

        } else {
            if (arm->pattern->tag != PAT_WILDCARD) {
                fatal_error("pattern should have been variant or wildcard");
            }

            // PAT_WILDCARD

            // We may assume that none of the check exprs so far are true
            struct Sexpr *assumption =
                make_list2_sexpr(
                    make_string_sexpr("not"),
                    disjunction(copy_sexpr(check_exprs)));
            cxt->path_condition = and_sexpr(copy_sexpr(backup_path_condition),
                                            assumption);

            // Verify the rhs
            struct Sexpr *rhs_expr = transform_term(tr, context, arm->rhs);

            // Undo the change to the path condition
            free_sexpr(cxt->path_condition);
            cxt->path_condition = NULL;

            // Create a sexpr for this arm
            // (We can just use "$wild" here, since we used "numbered" $wild
            // variables above, and we should hit this case only once per
            // match term)
            struct Sexpr *arm_expr = make_list2_sexpr(make_string_sexpr("$wild"), rhs_expr);
            *arm_tail = make_list1_sexpr(arm_expr);
            arm_tail = &(*arm_tail)->right;
        }
    }

    free_sexpr(check_exprs);

    // Restore the path condition
    cxt->path_condition = backup_path_condition;
    backup_path_condition = NULL;

    // Construct the final "match" expression
    return make_list3_sexpr(
        make_string_sexpr("match"),
        scrut_result,
        arm_exprs);
}

static void * verify_match_failure(void *context, struct Term *term, void *type_result)
{
    // this should be unreachable
    struct Sexpr *condition = make_string_sexpr("false");
    verify_condition(context, term->location, condition, "match exhaustive",
                     err_msg_nonexhaustive_match(term->location));
    free_sexpr(condition);

    // SMT-LIB does need an arm for all possible constructors
    // even if they are unreachable. Just return an arbitrary
    // value of the type in this case.
    struct Sexpr *any = make_string_sexpr("$ARBITRARY");
    make_instance(&any, make_list1_sexpr(verify_type(term->type)));
    return any;
}

static void * verify_sizeof(void *context, struct Term *term, void *type_result,
                            void *rhs_result)
{
    if (term->sizeof_data.rhs->type->array_data.sizes != NULL) {
        // Static-sized array type
        free_sexpr(rhs_result);
        return fixed_arr_size_sexpr(term->sizeof_data.rhs->type);

    } else {
        // Dynamic-sized or Incomplete array type

        struct Sexpr * array_type = verify_type(term->sizeof_data.rhs->type);

        // array_type is (instance $PROD something)
        // we change that to (instance $FLD1 something), and then apply that to the rhs.

        free_sexpr(array_type->right->left);
        array_type->right->left = make_string_sexpr("$FLD1");

        return make_list2_sexpr(array_type, rhs_result);
    }
}

static void * verify_allocated(void *context, struct Term *term, void *type_result,
                               void *rhs_result)
{
    struct Sexpr *rhs = rhs_result;
    struct Sexpr *expr = NULL;

    if (rhs->type == S_STRING) {
        expr = allocated_test_expr(term->allocated.rhs->type, rhs->string);
    } else {
        expr = allocated_test_expr(term->allocated.rhs->type, "$alloc_term");
        if (expr) {
            expr = make_list3_sexpr(make_string_sexpr("let"),
                                    make_list1_sexpr(make_list2_sexpr(make_string_sexpr("$alloc_term"),
                                                                      rhs)),
                                    expr);
            rhs = NULL;
        }
    }

    free_sexpr(rhs);

    if (!expr) {
        expr = make_string_sexpr("false");
    }

    return expr;
}

static void * nr_verify_array_proj(struct TermTransform *tr, void *context,
                                   struct Term *term, void *type_result)
{
    struct Sexpr *fol_lhs = transform_term(tr, context, term->array_proj.lhs);

    struct Type *lhs_type = term->array_proj.lhs->type;
    struct Sexpr *fol_type = verify_type(lhs_type);

    struct Sexpr *index =
        convert_indexes(context,
                        term->location,
                        lhs_type,
                        term->array_proj.indexes,
                        copy_sexpr(fol_lhs),
                        fol_type);

    struct Sexpr *expr;
    if (lhs_type->array_data.sizes == NULL) {
        expr = make_string_sexpr("$FLD0");
        make_instance(&expr, copy_sexpr(fol_type->right->right->left));
        expr = make_list2_sexpr(expr, fol_lhs);
    } else {
        expr = fol_lhs;
    }

    free_sexpr(fol_type);

    return make_list3_sexpr(make_string_sexpr("select"),
                            expr,
                            index);
}

static void * verify_op_term_list(void *context, struct OpTermList *op_term_list, void *rhs_result, void *next_result)
{
    return make_pair_sexpr(rhs_result, next_result);
}

static void * verify_name_term_list(void *context, struct NameTermList *name_term_list, void *term_result, void *next_result)
{
    return make_pair_sexpr(term_result, next_result);
}

// Returns a converted Sexpr. Should not return NULL.
struct Sexpr * verify_term(struct VContext *context, struct Term *term)
{
    struct TermTransform tr = {0};
    tr.transform_var = verify_var;
    tr.transform_default = verify_default;
    tr.transform_bool_literal = verify_bool_literal;
    tr.transform_int_literal = verify_int_literal;
    tr.transform_string_literal = verify_string_literal;
    tr.transform_array_literal = verify_array_literal;
    tr.transform_cast = verify_cast;
    tr.nr_transform_if = nr_verify_if;
    tr.transform_unop = verify_unop;
    tr.nr_transform_binop = nr_verify_binop;
    tr.nr_transform_let = nr_verify_let;
    tr.nr_transform_quantifier = nr_verify_quantifier;
    tr.nr_transform_call = nr_verify_call;
    tr.transform_record = verify_record;
    tr.transform_record_update = verify_record_update;
    tr.transform_field_proj = verify_field_proj;
    tr.transform_variant = verify_variant;
    tr.nr_transform_match = nr_verify_match;
    tr.transform_match_failure = verify_match_failure;
    tr.transform_sizeof = verify_sizeof;
    tr.transform_allocated = verify_allocated;
    tr.nr_transform_array_proj = nr_verify_array_proj;
    tr.transform_op_term_list = verify_op_term_list;
    tr.transform_name_term_list = verify_name_term_list;

    struct Sexpr *result = transform_term(&tr, context, term);

    return result;
}
