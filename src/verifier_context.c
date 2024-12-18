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
#include "names.h"
#include "sexpr.h"
#include "stacked_hash_table.h"
#include "util.h"
#include "verifier.h"
#include "verifier_context.h"
#include "verifier_dependency.h"
#include "verifier_types.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct StackedHashTable * push_verifier_stack(struct StackedHashTable *stack)
{
    struct StackedHashTable * layer = alloc(sizeof(struct StackedHashTable));
    layer->table = new_hash_table();
    layer->base = stack;
    return layer;
}

static void free_key_and_item(void *context, const char *key, void *value)
{
    free((char*)key);
    free_item((struct Item *)value);
}

struct StackedHashTable * pop_verifier_stack(struct StackedHashTable *stack)
{
    hash_table_for_each(stack->table, free_key_and_item, NULL);
    free_hash_table(stack->table);
    struct StackedHashTable *base = stack->base;
    free(stack);
    return base;
}

struct StackedHashTable * collapse_verifier_stack(struct StackedHashTable *stack)
{
    stacked_hash_table_collapse(stack, NULL, free_key_and_item);
    return pop_verifier_stack(stack);
}

void free_conditions(struct Condition *cond)
{
    while (cond) {
        free_sexpr(cond->expr);
        struct Condition *to_free = cond;
        cond = cond->next;
        free(to_free);
    }
}

void free_item(struct Item *item)
{
    if (item) {
        free_sexpr(item->fol_decl);
        free_sexpr(item->fol_axioms);
        free((char*)item->fol_name);
        free_sexpr(item->fol_type);
        free_sexpr(item->fol_generic_vars);
        free_sexpr(item->fol_dummies);
        free_conditions(item->preconds);
        free_conditions(item->postconds);
        free(item);
    }
}

static struct Condition * copy_condition(struct Condition *cond)
{
    if (cond) {
        struct Condition * result = alloc(sizeof(struct Condition));
        result->location = cond->location;
        result->expr = copy_sexpr(cond->expr);
        result->next = copy_condition(cond->next);
        return result;
    } else {
        return NULL;
    }
}

struct Item * copy_item(const struct Item *item)
{
    if (item) {
        struct Item *result = alloc(sizeof(struct Item));
        memset(result, 0, sizeof(struct Item));
        result->fol_decl = copy_sexpr(item->fol_decl);
        result->fol_axioms = copy_sexpr(item->fol_axioms);
        result->fol_name = copy_string(item->fol_name);
        result->fol_type = copy_sexpr(item->fol_type);
        result->fol_generic_vars = copy_sexpr(item->fol_generic_vars);
        result->fol_dummies = copy_sexpr(item->fol_dummies);
        result->preconds = copy_condition(item->preconds);
        result->postconds = copy_condition(item->postconds);
        memcpy(result->fingerprint, item->fingerprint, SHA256_HASH_LENGTH);
        return result;
    } else {
        return NULL;
    }
}

struct RefChain * copy_ref_chain(struct RefChain *ref)
{
    if (ref == NULL) return NULL;

    struct RefChain *result = alloc(sizeof(struct RefChain));
    result->type = ref->type;
    result->ref_type = ref->ref_type;
    result->fol_type = copy_sexpr(ref->fol_type);
    result->base = copy_ref_chain(ref->base);

    switch (ref->ref_type) {
    case RT_LOCAL_VAR:
        result->variable_name = ref->variable_name;
        result->postcond_new = ref->postcond_new;
        break;

    case RT_FIELD:
    case RT_VARIANT:
        result->index = ref->index;
        break;

    case RT_ARRAY_ELEMENT:
        result->array_index = copy_sexpr(ref->array_index);
        result->ndim = ref->ndim;
        result->fixed_size = ref->fixed_size;
        break;

    case RT_ARRAY_CAST:
        break;

    case RT_SEXPR:
        result->sexpr = copy_sexpr(ref->sexpr);
        break;
    }

    return result;
}

void free_ref_chain(struct RefChain *ref)
{
    while (ref) {
        struct RefChain *base = ref->base;
        free_sexpr(ref->fol_type);

        if (ref->ref_type == RT_ARRAY_ELEMENT) {
            free_sexpr(ref->array_index);
        } else if (ref->ref_type == RT_SEXPR) {
            free_sexpr(ref->sexpr);
        }

        free(ref);
        ref = base;
    }
}

void clear_refs_hash_table(struct HashTable *table)
{
    struct HashIterator *iter = new_hash_iterator(table);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        free_ref_chain((struct RefChain*)value);
    }
    free_hash_iterator(iter);
    hash_table_clear(table);
}

static bool is_true(struct Sexpr *expr)
{
    return expr->type == S_STRING && strcmp(expr->string, "true") == 0;
}

static bool is_false(struct Sexpr *expr)
{
    return expr->type == S_STRING && strcmp(expr->string, "false") == 0;
}

struct Sexpr *and_sexpr(struct Sexpr *lhs, struct Sexpr *rhs)
{
    if (is_true(lhs)) {
        // optimsation: (and true x) = x
        free_sexpr(lhs);
        return rhs;

    } else if (is_true(rhs)) {
        // optimisation: (and x true) = x
        free_sexpr(rhs);
        return lhs;

    } else if (lhs->type == S_PAIR && sexpr_equal_string(lhs->left, "and")) {
        // optimisation: (and (and <things>) x) = (and <things> x)

        struct Sexpr *node = lhs;
        while (node->right) {
            node = node->right;
        }
        node->right = make_list1_sexpr(rhs);

        return lhs;

    } else {
        // "normal" (unoptimised) case, return (and lhs rhs)
        return make_list3_sexpr(make_string_sexpr("and"), lhs, rhs);
    }
}

struct Sexpr *and_not_sexpr(struct Sexpr *lhs, struct Sexpr *rhs)
{
    return and_sexpr(lhs, make_list2_sexpr(make_string_sexpr("not"), rhs));
}

struct Sexpr *or_sexpr(struct Sexpr *lhs, struct Sexpr *rhs)
{
    // some useful optimisations:

    if (get_sexpr_list_length(rhs) == 2
        && sexpr_equal_string(rhs->left, "not")
        && sexpr_equal(rhs->right->left, lhs)) {
        // lhs = X
        // rhs = (not X)
        // result = true
        free_sexpr(lhs);
        free_sexpr(rhs);
        return make_string_sexpr("true");

    } else if (get_sexpr_list_length(lhs) == 3
               && get_sexpr_list_length(rhs) == 3
               && sexpr_equal_string(lhs->left, "and")
               && sexpr_equal_string(rhs->left, "and")
               && sexpr_equal(lhs->right->left, rhs->right->left)
               && get_sexpr_list_length(rhs->right->right->left) == 2
               && sexpr_equal_string(rhs->right->right->left->left, "not")
               && sexpr_equal(lhs->right->right->left, rhs->right->right->left->right->left)) {
        // lhs = (and X Y)
        // rhs = (and X (not Y))
        // result = X
        struct Sexpr *result = lhs->right->left;
        lhs->right->left = NULL;
        free_sexpr(lhs);
        free_sexpr(rhs);
        return result;

    } else {
        return make_list3_sexpr(make_string_sexpr("or"),
                                lhs,
                                rhs);
    }
}

// returns an expression of the form (=> CURRENT-PATH-CONDITION rhs).
// rhs is handed over.
// This is used at return statements (and in add_fact).
struct Sexpr * pc_implies(struct VContext *context, struct Sexpr *rhs)
{
    if (is_true(context->path_condition)) {
        // optimisation: (=> true x) = x
        return rhs;
    } else {
        return make_list3_sexpr(make_string_sexpr("=>"),
                                copy_sexpr(context->path_condition),
                                rhs);
    }
}

void make_ite_pc_expr(struct Sexpr *** ret_val_ptr, struct VContext *context, struct Sexpr *expr)
{
    if (**ret_val_ptr != NULL) {
        // A previous optimisation has changed (ite true x NULL) into x; the new
        // expr would go where the NULL is, but since the ite will never evaluate that
        // branch anyway, we can just ignore it.
        free_sexpr(expr);
        return;
    }

    if (is_true(context->path_condition)) {
        // optimisation: (ite true x NULL) = x
        **ret_val_ptr = expr;
    } else if (is_false(context->path_condition)) {
        // optimisation: (ite false x NULL) = NULL
        free_sexpr(expr);
    } else {
        **ret_val_ptr = make_list4_sexpr(make_string_sexpr("ite"),
                                        copy_sexpr(context->path_condition),
                                        expr,
                                        NULL);
        *ret_val_ptr = &((**ret_val_ptr)->right->right->right->left);
    }
}

void add_fact(struct VContext *context, struct Sexpr *fact)
{
    context->facts = make_pair_sexpr(pc_implies(context, fact), context->facts);
    ++context->num_facts;
}

int get_num_facts(struct VContext *context)
{
    return context->num_facts;
}

void revert_facts(struct VContext *context, int num)
{
    while (context->num_facts > num) {
        free_sexpr(context->facts->left);
        struct Sexpr *tail = context->facts->right;
        free(context->facts);
        context->facts = tail;
        -- context->num_facts;
    }
}


const char * int_type_string(const struct Type *type)
{
    if (type->tag != TY_FINITE_INT) {
        fatal_error("int_type_string called on wrong type");
    }

    if (type->int_data.is_signed) {
        switch (type->int_data.num_bits) {
        case 8: return "i8";
        case 16: return "i16";
        case 32: return "i32";
        case 64: return "i64";
        default: fatal_error("unknown integer size");
        }
    } else {
        switch (type->int_data.num_bits) {
        case 8: return "u8";
        case 16: return "u16";
        case 32: return "u32";
        case 64: return "u64";
        default: fatal_error("unknown integer size");
        }
    }
}


static char* make_local_name(const char *name, uintptr_t n)
{
    char suffix[30];
    if (n == 0) {
        suffix[0] = 0;
    } else {
        sprintf(suffix, ".%" PRIuPTR, n);
    }
    return copy_string_3("%", name, suffix);
}

struct Item *add_const_item(struct VContext *context,
                            const char *fol_name,
                            struct Type *type,
                            struct Sexpr *fol_type,
                            struct Sexpr *fol_term,
                            bool local)
{
    struct Item *item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));

    item->fol_axioms = NULL;

    if (fol_term) {
        // (define-fun fol_name () fol_type fol_term)
        item->fol_decl = make_list5_sexpr(
            make_string_sexpr("define-fun"),
            make_string_sexpr(fol_name),
            NULL,
            copy_sexpr(fol_type),
            fol_term);
    } else {
        // (declare-const fol_name fol_type)
        item->fol_decl = make_list3_sexpr(
            make_string_sexpr("declare-const"),
            make_string_sexpr(fol_name),
            copy_sexpr(fol_type));
        struct Sexpr * vexpr = validity_test_expr(type, fol_name);
        if (vexpr) {
            item->fol_axioms = make_list1_sexpr(
                make_list2_sexpr(
                    make_string_sexpr("assert"),
                    vexpr));
        }
    }

    item->fol_name = copy_string(fol_name);
    item->fol_type = fol_type;

    item->fol_generic_vars = NULL;
    item->fol_dummies = NULL;
    item->preconds = item->postconds = NULL;

    struct HashTable *table = local ? context->stack->table : context->stack->base->table;
    remove_existing_item(table, fol_name);
    hash_table_insert(table, fol_name, item);

    return item;
}

struct Item * add_tyvar_to_env(struct VContext *context, const char *name, bool local,
                               enum AllocLevel alloc_level)
{
    struct HashTable *env = local ? context->stack->table : context->stack->base->table;

    struct Item *item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));

    const char *fol_name = copy_string_2("%", name);

    // (declare-sort %^name 0)
    item->fol_decl = make_list3_sexpr(
        make_string_sexpr("declare-sort"),
        make_string_sexpr(fol_name),
        make_string_sexpr("0"));

    item->fol_axioms = NULL;

    item->fol_name = copy_string(fol_name);
    item->fol_type = NULL;

    item->fol_generic_vars = NULL;
    item->fol_dummies = NULL;
    item->preconds = NULL;
    item->postconds = NULL;

    hash_table_insert(env, copy_string(fol_name), item);
    struct Item * tyvar_item = item;
    item = NULL;


    // Add $default
    item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));

    const char *default_fol_name = copy_string_2("$default-", fol_name);

    // (declare-const $default-%^name %^name)
    item->fol_decl = make_list3_sexpr(
        make_string_sexpr("declare-const"),
        make_string_sexpr(default_fol_name),
        make_string_sexpr(fol_name));
    item->fol_name = copy_string(default_fol_name);

    if (hash_table_contains_key(env, default_fol_name)) {
        fatal_error("adding default_fol_name: key already exists");
    }

    hash_table_insert(env, default_fol_name, item);
    default_fol_name = NULL;
    item = NULL;


    // Add $allocated
    item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));

    const char *allocated_fol_name = copy_string_2("$allocated-", fol_name);

    if (alloc_level != ALLOC_UNKNOWN) {
        // (define-fun $allocated-%^name ((alloc_fol_var %^name)) Bool alloc_fol_term)

        struct Sexpr *alloc_expr = NULL;
        switch (alloc_level) {
        case ALLOC_ALWAYS:
            alloc_expr = make_string_sexpr("true");
            break;

        case ALLOC_NEVER:
            alloc_expr = make_string_sexpr("false");
            break;

        case ALLOC_IF_NOT_DEFAULT:
            alloc_expr = make_list3_sexpr(
                make_string_sexpr("distinct"),
                make_string_sexpr("$x"),
                make_string_sexpr_handover(copy_string_2("$default-", fol_name)));
            break;

        case ALLOC_UNKNOWN:
            fatal_error("unreachable");
        }

        item->fol_decl = make_list5_sexpr(
            make_string_sexpr("define-fun"),
            make_string_sexpr(allocated_fol_name),
            make_list1_sexpr(make_list2_sexpr(make_string_sexpr("$x"),
                                              make_string_sexpr(fol_name))),
            make_string_sexpr("Bool"),
            alloc_expr);

    } else {
        // (declare-fun $allocated-%^name (%^name) Bool)
        item->fol_decl = make_list4_sexpr(
            make_string_sexpr("declare-fun"),
            make_string_sexpr(allocated_fol_name),
            make_list1_sexpr(make_string_sexpr(fol_name)),
            make_string_sexpr("Bool"));
    }

    item->fol_name = copy_string(allocated_fol_name);

    if (hash_table_contains_key(env, allocated_fol_name)) {
        fatal_error("adding allocated_fol_name: key already exists");
    }

    hash_table_insert(env, allocated_fol_name, item);
    allocated_fol_name = NULL;
    item = NULL;

    // Add $valid
    item = alloc(sizeof(struct Item));
    memset(item, 0, sizeof(struct Item));

    const char *valid_fol_name = copy_string_2("$valid-", fol_name);

    // (declare-fun $valid-%^name (%^name) Bool)
    item->fol_decl = make_list4_sexpr(
        make_string_sexpr("declare-fun"),
        make_string_sexpr(valid_fol_name),
        make_list1_sexpr(make_string_sexpr(fol_name)),
        make_string_sexpr("Bool"));
    item->fol_name = copy_string(valid_fol_name);

    if (hash_table_contains_key(env, valid_fol_name)) {
        fatal_error("adding valid_fol_name: key already exists");
    }

    hash_table_insert(env, valid_fol_name, item);
    valid_fol_name = NULL;

    free((char*)fol_name);
    fol_name = NULL;

    return tyvar_item;
}

void add_tyvars_to_env(struct VContext *context, const struct TyVarList *tyvars)
{
    while (tyvars) {
        // Note: It is unknown whether these tyvars are allocated or not.
        add_tyvar_to_env(context, tyvars->name, true, ALLOC_UNKNOWN);
        tyvars = tyvars->next;
    }
}

void remove_existing_item(struct HashTable *table, const char *fol_name)
{
    const char *existing_key;
    void *existing_value;
    hash_table_lookup_2(table, fol_name, &existing_key, &existing_value);
    if (existing_key) {
        hash_table_remove(table, existing_key);
        free((char*)existing_key);
        free_item(existing_value);
    }
}

void remove_facts(struct VContext *cxt, const char *fol_name)
{
    struct Sexpr ** ptr = &cxt->facts;

    struct HashTable *names = new_hash_table();
    struct HashTable *scratch = new_hash_table();

    while (*ptr) {
        get_free_var_names_in_sexpr((*ptr)->left, names, scratch);
        if (hash_table_contains_key(names, fol_name)) {
            free_sexpr((*ptr)->left);
            struct Sexpr *right = (*ptr)->right;
            free(*ptr);
            *ptr = right;
            --cxt->num_facts;
        } else {
            ptr = &(*ptr)->right;
        }
        hash_table_clear(names);
    }

    free_hash_table(names);
    free_hash_table(scratch);
}

void make_instance(struct Sexpr **expr,    // modified in place
                   struct Sexpr *tyargs)   // handed over
{
    if (tyargs != NULL) {
        *expr = make_list3_sexpr(make_string_sexpr("instance"),
                                 *expr,
                                 tyargs);
    }
}

static void remove_from_list(const char *string, struct Sexpr **list)
{
    while (*list) {
        if (sexpr_equal_string((*list)->left, string)) {
            struct Sexpr *to_free = *list;
            *list = (*list)->right;
            free_sexpr(to_free->left);
            free(to_free);
        } else {
            list = &(*list)->right;
        }
    }
}

// Assumes that "list" is a non-empty list of valid FOL-exprs.
// Returns true if list is (X (not X)) or ((not X) X), for any sexpr X.
static bool item_and_its_negation(struct Sexpr *list)
{
    if (list->right && !list->right->right) {
        // length 2 list
        struct Sexpr *item1 = list->left;
        struct Sexpr *item2 = list->right->left;
        return (item1->type == S_PAIR &&
                sexpr_equal_string(item1->left, "not") &&
                sexpr_equal(item1->right->left, item2))
            || (item2->type == S_PAIR &&
                sexpr_equal_string(item2->left, "not") &&
                sexpr_equal(item2->right->left, item1));
    } else {
        return false;
    }
}

struct Sexpr *conjunction(struct Sexpr *list)  // handed over
{
    remove_from_list("true", &list);
    if (list == NULL) {
        return make_string_sexpr("true");

    } else if (list->type == S_STRING) {
        fatal_error("not a list");

    } else if (list->right == NULL) {
        struct Sexpr *result = list->left;
        free(list);
        return result;

    } else if (item_and_its_negation(list)) {
        free_sexpr(list);
        return make_string_sexpr("false");

    } else {
        return make_pair_sexpr(make_string_sexpr("and"), list);
    }
}

struct Sexpr *disjunction(struct Sexpr *list)  // handed over
{
    remove_from_list("false", &list);
    if (list == NULL) {
        return make_string_sexpr("false");

    } else if (list->type == S_STRING) {
        fatal_error("not a list");

    } else if (list->right == NULL) {
        struct Sexpr *result = list->left;
        free(list);
        return result;

    } else if (item_and_its_negation(list)) {
        free_sexpr(list);
        return make_string_sexpr("true");

    } else {
        return make_pair_sexpr(make_string_sexpr("or"), list);
    }
}

void analyse_variant(const char *variant_name,
                     struct Type *type,
                     struct Type ** payload_type_out,
                     struct Sexpr ** ctor_out,
                     struct Sexpr ** tester_out,
                     struct Sexpr ** selector_out)
{
    int num = 0;
    bool found = false;
    for (struct NameTypeList *variant = type->variant_data.variants; variant; variant = variant->next) {
        if (strcmp(variant->name, variant_name) == 0) {
            *payload_type_out = variant->type;
            found = true;
            break;
        }
        ++num;
    }

    if (!found) {
        fatal_error("analyse_variant: not found");
    }

    struct Sexpr *type_list = verify_name_type_list(type->variant_data.variants);

    char buf[30];
    sprintf(buf, "$IN%d", num);
    struct Sexpr *ctor = make_string_sexpr(buf);
    make_instance(&ctor, copy_sexpr(type_list));

    if (ctor_out) {
        *ctor_out = copy_sexpr(ctor);
    }

    *tester_out =
        make_list3_sexpr(
            make_string_sexpr("_"),
            make_string_sexpr("is"),
            ctor);

    if (selector_out) {
        sprintf(buf, "$INF%d", num);
        *selector_out = make_string_sexpr(buf);
        make_instance(selector_out, type_list);
    } else {
        free_sexpr(type_list);
    }
}

void get_modified_vars_deref(struct VContext *context,
                             struct HashTable *names,
                             struct Statement *stmt)
{
    struct HashTable *temp_names = new_hash_table();
    get_modified_var_names(temp_names, stmt);

    struct HashIterator *iter = new_hash_iterator(temp_names);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct RefChain *ref = hash_table_lookup(context->refs, key);
        if (ref) {
            while (ref->base) ref = ref->base;
            if (ref->ref_type != RT_LOCAL_VAR) {
                fatal_error("modified var ref has unexpected ref_type");
            }
            hash_table_insert(names, ref->variable_name, ref->type);
        } else {
            hash_table_insert(names, key, value);
        }
    }

    free_hash_iterator(iter);
    free_hash_table(temp_names);
}


struct Sexpr *copy_record_fields(struct Sexpr *record,
                                 struct Sexpr *field_types)
{
    struct Sexpr *result = make_string_sexpr("$PROD");
    make_instance(&result, copy_sexpr(field_types));
    result = make_list1_sexpr(result);
    struct Sexpr **tail = &result->right;

    uint32_t num = 0;
    for (struct Sexpr *node = field_types; node; node = node->right) {
        char fld[30];
        sprintf(fld, "$FLD%" PRIu32, num);

        struct Sexpr *new_sexpr = make_string_sexpr(fld);
        make_instance(&new_sexpr, copy_sexpr(field_types));

        new_sexpr = make_list2_sexpr(new_sexpr, copy_sexpr(record));

        *tail = make_list1_sexpr(new_sexpr);
        tail = &(*tail)->right;

        ++num;
    }

    return result;
}

struct Sexpr * array_index_type(int ndim)
{
    if (ndim == 1) {
        return make_string_sexpr("Int");
    } else {
        struct Sexpr * types = NULL;
        struct Sexpr ** tail = &types;
        for (int i = 0; i < ndim; ++i) {
            *tail = make_list1_sexpr(make_string_sexpr("Int"));
            tail = &(*tail)->right;
        }
        struct Sexpr *result = make_string_sexpr("$PROD");
        make_instance(&result, types);
        return result;
    }
}

static bool is_unsigned(const struct OpTermList *term)
{
    return term
        && term->rhs->type->tag == TY_FINITE_INT
        && !term->rhs->type->int_data.is_signed;
}

struct Sexpr * array_index_in_range(int ndim, const char *idx_name, const char *size_name,
                                    const struct OpTermList *idx_terms, bool assume_nonneg)
{
    if (ndim == 1) {
        struct Sexpr * lt_size =
            make_list3_sexpr(
               make_string_sexpr("<"),
               make_string_sexpr(idx_name),
               make_string_sexpr(size_name));
        if (assume_nonneg || is_unsigned(idx_terms)) {
            return lt_size;
        } else {
            return make_list3_sexpr(
               make_string_sexpr("and"),
               make_list3_sexpr(
                   make_string_sexpr(">="),
                   make_string_sexpr(idx_name),
                   make_string_sexpr("0")),
               lt_size);
        }
    } else {

        struct Sexpr *idx_pattern = make_list1_sexpr(array_index_type(ndim));
        struct Sexpr **idx_pattern_tail = &idx_pattern->right;

        struct Sexpr *size_pattern = make_list1_sexpr(array_index_type(ndim));
        struct Sexpr **size_pattern_tail = &size_pattern->right;

        struct Sexpr *conditions = NULL;
        struct Sexpr **cond_tail = &conditions;

        for (int i = 0; i < ndim; ++i) {
            char idx[30];
            sprintf(idx, "$idx%d", i);

            char size[30];
            sprintf(size, "$size%d", i);

            *idx_pattern_tail = make_list1_sexpr(make_string_sexpr(idx));
            idx_pattern_tail = &(*idx_pattern_tail)->right;

            *size_pattern_tail = make_list1_sexpr(make_string_sexpr(size));
            size_pattern_tail = &(*size_pattern_tail)->right;

            struct Sexpr *lt_size =
                make_list3_sexpr(
                     make_string_sexpr("<"),
                     make_string_sexpr(idx),
                     make_string_sexpr(size));
            if (assume_nonneg || is_unsigned(idx_terms)) {
                *cond_tail = make_list1_sexpr(lt_size);
                cond_tail = &(*cond_tail)->right;
            } else {
                *cond_tail = make_list2_sexpr(
                     make_list3_sexpr(
                         make_string_sexpr(">="),
                         make_string_sexpr(idx),
                         make_string_sexpr("0")),
                     lt_size);
                cond_tail = &(*cond_tail)->right->right;
            }
            idx_terms = idx_terms ? idx_terms->next : NULL;
        }

        return make_list3_sexpr(
            make_string_sexpr("match"),
            make_string_sexpr(idx_name),
            make_list1_sexpr(
                make_list2_sexpr(
                    idx_pattern,
                    make_list3_sexpr(
                        make_string_sexpr("match"),
                        make_string_sexpr(size_name),
                        make_list1_sexpr(
                            make_list2_sexpr(
                                size_pattern,
                                conjunction(conditions)))))));
    }
}

static uintptr_t bump_local(struct VContext *context, const char *local_name)
{
    // Make a new "version number" for this variable
    uintptr_t version = (uintptr_t) hash_table_lookup(context->local_counter, local_name);
    hash_table_insert(context->local_counter,
                      local_name,
                      (void*)(version + 1));
    hash_table_insert(context->local_to_version,
                      local_name,
                      (void*)(version + 1));
    return version;
}

struct Item * update_local(struct VContext *context,
                           const char *local_name,
                           struct Type *type,
                           struct Sexpr *fol_type,
                           struct Sexpr *fol_term)
{
    uintptr_t version = bump_local(context, local_name);
    return add_const_item(context,
                          make_local_name(local_name, version),
                          type,
                          fol_type,
                          fol_term,
                          true);
}

void ensure_nonzero_name(struct VContext *context, const char *local_name)
{
    if (!hash_table_contains_key(context->local_counter, local_name)) {
        bump_local(context, local_name);
    }
}

char* lookup_local(struct VContext *context, const char *local_name)
{
    uintptr_t version = (uintptr_t) hash_table_lookup(context->local_to_version, local_name);
    if (version == 0) {
        return NULL;
    }
    return make_local_name(local_name, version - 1);
}

struct HashTable * snapshot_variable_versions(struct VContext *context,
                                              struct HashTable *modified_vars)
{
    struct HashTable *result = new_hash_table();

    struct HashIterator *iterator = new_hash_iterator(modified_vars);
    const char *var_name;
    void *value;
    while (hash_iterator_next(iterator, &var_name, &value)) {
        void *value = hash_table_lookup(context->local_to_version, var_name);
        if (value) {
            hash_table_insert(result, var_name, value);
        }
    }
    free_hash_iterator(iterator);

    return result;
}

static void update_variable_for_if(struct VContext *context,
                                   struct Sexpr *cond_expr,
                                   const char *local_name,
                                   uintptr_t then_num,
                                   uintptr_t else_num)
{
    // find the old variable (assumed to be a declare-const) in the env,
    // and find its FOL type
    char *old_fol_name = lookup_local(context, local_name);
    struct Sexpr *fol_type = NULL;
    if (old_fol_name != NULL) {
        struct Item *item = hash_table_lookup(context->stack->table, old_fol_name); // lookup in local env
        fol_type = copy_sexpr(item->fol_type);
        free(old_fol_name);
        old_fol_name = NULL;
    }

    const char *then_fol_name = make_local_name(local_name, then_num - 1);
    const char *else_fol_name = make_local_name(local_name, else_num - 1);

    // update the variable, as if doing an assignment
    // the new value is an ite-expression
    struct Sexpr *ite_expr =
        make_list4_sexpr(
            make_string_sexpr("ite"),
            copy_sexpr(cond_expr),
            make_string_sexpr_handover(then_fol_name),
            make_string_sexpr_handover(else_fol_name));

    update_local(context, local_name, NULL, fol_type, ite_expr);
}

void resolve_if_branches(struct VContext *context,
                         struct Sexpr *cond,    // shared
                         bool use_snapshot_when,
                         struct HashTable *snapshot)   // shared
{
    struct HashIterator *iterator = new_hash_iterator(snapshot);
    const char *local_name;
    void *value;
    while (hash_iterator_next(iterator, &local_name, &value)) {
        uintptr_t from_snap = (uintptr_t) value;
        uintptr_t exist = (uintptr_t) hash_table_lookup(context->local_to_version, local_name);

        uintptr_t then_num = use_snapshot_when ? from_snap : exist;
        uintptr_t else_num = use_snapshot_when ? exist : from_snap;

        update_variable_for_if(context, cond, local_name, then_num, else_num);
    }
    free_hash_iterator(iterator);
}

void revert_to_snapshot(struct VContext *context,
                        struct HashTable *snapshot)
{
    struct HashIterator *iterator = new_hash_iterator(snapshot);
    const char *local_name;
    void *value;
    while (hash_iterator_next(iterator, &local_name, &value)) {
        uintptr_t updated_num = (uintptr_t) value;
        hash_table_insert(context->local_to_version, local_name, (void*)updated_num);
    }
    free_hash_iterator(iterator);
}

struct Sexpr *for_all_array_elt(int ndim,
                                struct Sexpr *expr,
                                struct Sexpr *elt_type)
{
    struct Sexpr *inrange = array_index_in_range(ndim, "$idx", "$size", NULL, false);

    struct Sexpr *arbitrary_elt = make_string_sexpr("$ARBITRARY");
    make_instance(&arbitrary_elt, make_list1_sexpr(elt_type));
    elt_type = NULL;

    struct Sexpr *is_arbitrary =
        make_list3_sexpr(
            make_string_sexpr("="),
            make_string_sexpr("$elt"),
            arbitrary_elt);
    arbitrary_elt = NULL;

    struct Sexpr *ite = make_list4_sexpr(
        make_string_sexpr("ite"),
        inrange,
        expr,
        is_arbitrary);
    expr = is_arbitrary = NULL;

    struct Sexpr *let = make_list3_sexpr(
        make_string_sexpr("let"),
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr("$elt"),
                make_list3_sexpr(
                    make_string_sexpr("select"),
                    make_string_sexpr("$arr"),
                    make_string_sexpr("$idx")))),
        ite);
    ite = NULL;

    return make_list3_sexpr(
        make_string_sexpr("forall"),
        make_list1_sexpr(
            make_list2_sexpr(
                make_string_sexpr("$idx"),
                array_index_type(ndim))),
        let);
}

// create "match arr_expr with (arr_name,size_name) => rhs_expr"
// arr_expr, rhs_expr are handed over. arr_name, size_name are copied.
struct Sexpr *match_arr_size(const char *arr_name, const char *size_name,
                             struct Sexpr *arr_expr, struct Type *array_type, struct Sexpr *rhs_expr)
{
    if (array_type->tag != TY_ARRAY || array_type->array_data.sizes != NULL) {
        fatal_error("match_arr_size: wrong type");
    }
    return make_list3_sexpr(
        make_string_sexpr("match"),
        arr_expr,
        make_list1_sexpr(   // 1 arm
            make_list2_sexpr(   // arm = pattern + rhs
                make_list3_sexpr(   // pattern = ctor + var + var
                    verify_type(array_type),     // ctor = array type ($PROD)
                    make_string_sexpr(arr_name),
                    make_string_sexpr(size_name)),
                rhs_expr)));
}

struct Sexpr *fixed_arr_size_sexpr(struct Type *array_type)
{
    if (array_type->tag != TY_ARRAY || array_type->array_data.sizes == NULL) {
        fatal_error("fixed_arr_size_sexpr: wrong type");
    }
    struct TypeData_Array *data = &array_type->array_data;
    if (data->ndim == 1) {
        return make_string_sexpr(data->sizes[0]->int_literal.data);
    } else {
        struct Sexpr *list = NULL;
        struct Sexpr *ints = NULL;
        struct Sexpr **tail = &list;
        struct Sexpr **ints_tail = &ints;
        for (int i = 0; i < data->ndim; ++i) {
            *tail = make_list1_sexpr(make_string_sexpr(data->sizes[i]->int_literal.data));
            *ints_tail = make_list1_sexpr(make_string_sexpr("Int"));
            tail = &(*tail)->right;
            ints_tail = &(*ints_tail)->right;
        }
        struct Sexpr *prod = make_string_sexpr("$PROD");
        make_instance(&prod, ints);
        ints = NULL;
        return make_pair_sexpr(prod, list);
    }
}

struct Sexpr *make_record_predicate(
    struct VContext *context,
    struct Type *type,
    const char *var_name,
    struct Sexpr * (*make_child_predicate)(struct VContext *, struct Type *, const char *),
    struct Sexpr * (*combine_func)(struct Sexpr *))
{
    // (match var_name
    //   ((((instance $PROD types) $v0 $v1 .. $vn)
    //     (and valid_$v0 valid_$v1 .. valid_$vn)))
    if (type->record_data.fields) {
        struct Sexpr *pattern = make_string_sexpr("$PROD");
        make_instance(&pattern, verify_name_type_list(type->record_data.fields));

        pattern = make_list1_sexpr(pattern);
        struct Sexpr **pattern_tail = &pattern->right;

        struct Sexpr *conditions = NULL;
        struct Sexpr **cond_tail = &conditions;

        int num = 0;
        for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
            char buf[30];
            sprintf(buf, "$v%d", num++);

            *pattern_tail = make_list1_sexpr(make_string_sexpr(buf));
            pattern_tail = &(*pattern_tail)->right;

            struct Sexpr *new_cond = make_child_predicate(context, field->type, buf);
            if (new_cond) {
                *cond_tail = make_list1_sexpr(new_cond);
                cond_tail = &(*cond_tail)->right;
            }
        }

        if (conditions != NULL) {
            return make_list3_sexpr(
                make_string_sexpr("match"),
                make_string_sexpr(var_name),
                make_list1_sexpr(
                    make_list2_sexpr(pattern, combine_func(conditions))));
        } else {
            free_sexpr(pattern);
            free_sexpr(conditions);
            return NULL;
        }
    } else {
        // trivial case, empty record
        return NULL;
    }
}

struct Sexpr *make_variant_predicate(
    struct VContext *context,
    struct Type *type,
    const char *var_name,
    struct Sexpr * (*make_child_predicate)(struct VContext *, struct Type *, const char *),
    struct Sexpr * (*combine_func)(struct Sexpr *))
{
    // (match var_name
    //   ( (((instance $IN0 types) $v) valid_$v)
    //     ...
    //     (((instance $INn types) $v) valid_$v) ))
    {
        struct Sexpr *arms = NULL;
        struct Sexpr **arm_tail = &arms;

        bool found_nontrivial = false;

        int num = 0;
        for (struct NameTypeList *variant = type->variant_data.variants; variant; variant = variant->next) {
            char buf[30];
            sprintf(buf, "$IN%d", num++);

            struct Sexpr *arm = make_string_sexpr(buf);
            make_instance(&arm, verify_name_type_list(type->variant_data.variants));
            arm = make_list2_sexpr(arm, make_string_sexpr("$v"));

            struct Sexpr *vexpr = make_child_predicate(context, variant->type, "$v");
            if (vexpr) {
                found_nontrivial = true;
            } else {
                vexpr = combine_func(NULL);
            }

            arm = make_list2_sexpr(arm, vexpr);

            *arm_tail = make_list1_sexpr(arm);
            arm_tail = &(*arm_tail)->right;
        }

        if (found_nontrivial) {
            return make_list3_sexpr(
                make_string_sexpr("match"),
                make_string_sexpr(var_name),
                arms);
        } else {
            free_sexpr(arms);
            return NULL;
        }
    }
}

static struct Sexpr *wrap_validity_test_expr(struct VContext *cxt, struct Type *type, const char *var_name) {
    return validity_test_expr(type, var_name);
}

struct Sexpr *validity_test_expr(struct Type *type, const char *var_name)
{
    switch (type->tag) {
    case TY_UNIVAR:
        fatal_error("TY_UNIVAR should have been removed");

    case TY_VAR:
        ;
        char *valid_name = copy_string_2("$valid-%", type->var_data.name);
        return make_list2_sexpr(make_string_sexpr_handover(valid_name),
                                make_string_sexpr(var_name));

    case TY_BOOL:
        return NULL;

    case TY_FINITE_INT:
        return make_list2_sexpr(
            make_string_sexpr_handover(copy_string_2("$in_range_", int_type_string(type))),
            make_string_sexpr(var_name));

    case TY_MATH_INT:
    case TY_MATH_REAL:
        return NULL;

    case TY_RECORD:
        return make_record_predicate(NULL, type, var_name, wrap_validity_test_expr, conjunction);

    case TY_VARIANT:
        return make_variant_predicate(NULL, type, var_name, wrap_validity_test_expr, conjunction);

    case TY_ARRAY:
        if (type->array_data.sizes != NULL) {
            // Fixed-sized array.

            // Make an expression saying that all array elements in range are
            // valid, and all out-of-range are equal to $ARBITRARY at that type.
            struct Type *elt_type = type->array_data.element_type;
            struct Sexpr *elt_valid = validity_test_expr(elt_type, "$elt");
            if (elt_valid == NULL) {
                elt_valid = make_string_sexpr("true");
            }

            return make_list3_sexpr(
                make_string_sexpr("let"),
                make_list2_sexpr(
                    make_list2_sexpr(
                        make_string_sexpr("$arr"),
                        make_string_sexpr(var_name)),
                    make_list2_sexpr(
                        make_string_sexpr("$size"),
                        fixed_arr_size_sexpr(type))),
                for_all_array_elt(
                    type->array_data.ndim,
                    elt_valid,
                    verify_type(elt_type)));

        } else {
            // Allocatable or "incomplete-type" array.

            // First make an expression saying that the size is valid.
            struct Type *elt_type = type->array_data.element_type;
            int ndim = type->array_data.ndim;
            struct Sexpr *size_valid = NULL;

            if (ndim == 1) {
                size_valid = make_list2_sexpr(make_string_sexpr("$in_range_u64"),
                                              make_string_sexpr("$size"));

            } else {
                struct Sexpr *pattern = make_list1_sexpr(array_index_type(ndim));
                struct Sexpr **pattern_tail = &pattern->right;

                struct Sexpr *conditions = NULL;
                struct Sexpr **cond_tail = &conditions;

                for (int i = 0; i < ndim; ++i) {
                    char buf[30];
                    sprintf(buf, "$v%d", i);

                    *pattern_tail = make_list1_sexpr(make_string_sexpr(buf));
                    pattern_tail = &(*pattern_tail)->right;

                    struct Sexpr *new_cond = make_list2_sexpr(make_string_sexpr("$in_range_u64"),
                                                              make_string_sexpr(buf));
                    *cond_tail = make_list1_sexpr(new_cond);
                    cond_tail = &(*cond_tail)->right;
                }

                size_valid = make_list3_sexpr(make_string_sexpr("match"),
                                              make_string_sexpr("$size"),
                                              make_list1_sexpr(make_list2_sexpr(pattern, conjunction(conditions))));
            }

            // Make an expression saying that all array elements in range are valid,
            // and all out-of-range are equal to $ARBITRARY at that type.
            struct Sexpr *elt_valid = validity_test_expr(elt_type, "$elt");
            if (elt_valid == NULL) {
                elt_valid = make_string_sexpr("true");
            }

            struct Sexpr *size_and_elts_valid = make_list3_sexpr(
                make_string_sexpr("and"),
                size_valid,
                for_all_array_elt(ndim, elt_valid, verify_type(elt_type)));

            return match_arr_size(
                "$arr", "$size",
                make_string_sexpr(var_name),
                type,
                size_and_elts_valid);
        }

    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
    case TY_APP:
        fatal_error("validity_test_expr - unexpected case");
    }

    fatal_error("validity_test_expr - unknown type");
}

struct Sexpr * insert_validity_condition(struct VContext *context,
                                         enum Quantifier quant,
                                         struct Type *type,
                                         struct Sexpr *fol_var,
                                         struct Sexpr *term)
{
    if (fol_var->type != S_STRING) {
        fatal_error("insert_validity_condition: not a variable");
    }
    struct Sexpr *valid_expr = validity_test_expr(type, fol_var->string);
    if (valid_expr) {
        // (XX valid_expr TERM)
        //   where XX is "=>" for FORALL, or "and" for EXISTS
        term = make_list3_sexpr(
            make_string_sexpr(quant == QUANT_FORALL ? "=>" : "and"),
            valid_expr,
            term);
    }
    return term;
}

struct Sexpr * insert_validity_conditions(struct VContext *context,
                                          enum Quantifier quant,
                                          struct FunArg *fun_args,
                                          struct Sexpr *funapp_sexpr,
                                          struct Sexpr *term)
{
    if (funapp_sexpr->type == S_PAIR) {
        funapp_sexpr = funapp_sexpr->right;  // skip the function name itself
        while (funapp_sexpr) {
            term = insert_validity_condition(context, quant, fun_args->type, funapp_sexpr->left, term);
            fun_args = fun_args->next;
            funapp_sexpr = funapp_sexpr->right;
        }
    }
    return term;
}


struct Sexpr *allocated_test_expr(struct VContext *context,
                                  struct Type *type,
                                  const char *var_name)
{
    switch (type->tag) {
    case TY_UNIVAR:
        fatal_error("TY_UNIVAR should have been removed");

    case TY_VAR:
        ;
        char *alloc_name = copy_string_2("$allocated-%", type->var_data.name);
        return make_list2_sexpr(make_string_sexpr_handover(alloc_name),
                                make_string_sexpr(var_name));

    case TY_BOOL:
    case TY_FINITE_INT:
    case TY_MATH_INT:
    case TY_MATH_REAL:
        return NULL;

    case TY_RECORD:
        return make_record_predicate(context, type, var_name, allocated_test_expr, disjunction);

    case TY_VARIANT:
        return make_variant_predicate(context, type, var_name, allocated_test_expr, disjunction);

    case TY_ARRAY:
        if (type->array_data.sizes != NULL) {
            // A fixed-array is allocated if any of its elements is...
            struct Type *elt_type = type->array_data.element_type;
            int ndim = type->array_data.ndim;

            // "$elt" is allocated
            struct Sexpr *elt_alloc = allocated_test_expr(context, elt_type, "$elt");

            if (elt_alloc == NULL) {
                // This array is never allocated, because it is fixed-size
                // and its elements are of a non-allocated type.
                return NULL;
            }

            // "$idx" is in range
            struct Sexpr *inrange = array_index_in_range(ndim, "$idx", "$size", NULL, false);

            // "$idx" is in range, and the element at $idx is allocated
            struct Sexpr *inrange_and_alloc =
                make_list3_sexpr(
                    make_string_sexpr("and"),
                    make_list3_sexpr(
                        make_string_sexpr("let"),
                        make_list1_sexpr(
                            make_list2_sexpr(
                                make_string_sexpr("$size"),
                                fixed_arr_size_sexpr(type))),
                        inrange),
                    make_list3_sexpr(
                        make_string_sexpr("let"),
                        make_list1_sexpr(
                            make_list2_sexpr(
                                make_string_sexpr("$elt"),
                                make_list3_sexpr(
                                    make_string_sexpr("select"),
                                    make_string_sexpr(var_name),
                                    make_string_sexpr("$idx")))),
                        elt_alloc));

            // there exists $idx such that inrange_and_alloc is true
            return make_list3_sexpr(
                make_string_sexpr("exists"),
                make_list1_sexpr(
                    make_list2_sexpr(
                        make_string_sexpr("$idx"),
                        array_index_type(ndim))),
                inrange_and_alloc);

        } else if (type->array_data.resizable) {
            // A resizable array type is allocated if its size is nonzero.
            int ndim = type->array_data.ndim;
            struct Sexpr *size_zero = NULL;

            if (ndim == 1) {
                size_zero = make_list3_sexpr(make_string_sexpr("distinct"),
                                             make_string_sexpr("$size"),
                                             make_string_sexpr("0"));
            } else {
                struct Sexpr *pattern = make_list1_sexpr(array_index_type(ndim));
                struct Sexpr **pattern_tail = &pattern->right;

                struct Sexpr *conditions = NULL;
                struct Sexpr **cond_tail = &conditions;

                for (int i = 0; i < ndim; ++i) {
                    char buf[30];
                    sprintf(buf, "$v%d", i);

                    *pattern_tail = make_list1_sexpr(make_string_sexpr(buf));
                    pattern_tail = &(*pattern_tail)->right;

                    struct Sexpr *new_cond = make_list3_sexpr(make_string_sexpr("distinct"),
                                                              make_string_sexpr(buf),
                                                              make_string_sexpr("0"));
                    *cond_tail = make_list1_sexpr(new_cond);
                    cond_tail = &(*cond_tail)->right;
                }

                size_zero = make_list3_sexpr(make_string_sexpr("match"),
                                             make_string_sexpr("$size"),
                                             make_list1_sexpr(make_list2_sexpr(pattern, conjunction(conditions))));
            }

            return match_arr_size(
                "$arr", "$size",
                make_string_sexpr(var_name),
                type,
                size_zero);

        } else {
            // The allocated status of an "incomplete" array type shouldn't
            // ever be needed, currently.
            fatal_error("checking if incomplete-type array is allocated - not currently supported");
        }

    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
    case TY_APP:
        fatal_error("allocated_test_expr - unexpected case");
    }

    fatal_error("allocated_test_expr - unknown type");
}

struct Sexpr * non_allocated_condition(struct VContext *context,
                                       struct Type *type,
                                       struct Sexpr *fol_term)   // copied/referenced only
{
    struct Sexpr *cond;
    if (fol_term->type == S_STRING) {
        cond = allocated_test_expr(context, type, fol_term->string);
    } else {
        cond = allocated_test_expr(context, type, "$copied");
    }

    if (cond) {
        cond = make_list2_sexpr(make_string_sexpr("not"), cond);

        if (fol_term->type != S_STRING) {
            cond = make_list3_sexpr(
                make_string_sexpr("let"),
                make_list1_sexpr(make_list2_sexpr(make_string_sexpr("$copied"), copy_sexpr(fol_term))),
                cond);
        }
    }

    return cond;
}
