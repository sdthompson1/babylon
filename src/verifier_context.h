/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_CONTEXT_H
#define VERIFIER_CONTEXT_H

#include <stdbool.h>
#include <stdint.h>

struct CacheDb;
struct FunArg;
struct HashTable;
struct Sexpr;


//-------------------------------------------------------------------------------
// Verifier env
//-------------------------------------------------------------------------------

// A VerifierEnv is a hash table in which the keys are global FOL
// names (beginning with "%" or "$") and the values are Items
// (defined below). Both are allocated.
struct VerifierEnv {
    struct HashTable *table;

    // this is used for tracking string literals and fixed-sized array defaults
    struct HashTable *string_names;
};

struct Condition {
    struct Location location;
    struct Sexpr *expr;
    struct Condition *next;
};

// Note: if adding new fields to Item, remember to update copy_item in
// verifier_context.c.
struct Item {
    struct Sexpr *fol_decl;     // FOL cmd e.g. (declare-fun ...). Could be NULL
    struct Sexpr *fol_axioms;   // list of FOL cmds e.g. ((assert ...) ...)

    const char *fol_name;
    struct Sexpr *fol_type;     // only needed for variables that can be updated using update_local. can be NULL for anything else.

    struct Sexpr *fol_generic_vars;   // list of strings (generic params needed for pre/post conds and the definition).
    struct Sexpr *fol_dummies;  // list of strings (dummy var names used in pre/post conds).
    struct Condition *preconds;
    struct Condition *postconds;

    uint8_t fingerprint[SHA256_HASH_LENGTH];  // only nonzero for global decl items.
};


//-------------------------------------------------------------------------------
// Verification context struct
//-------------------------------------------------------------------------------

struct VContext {
    // Mappings from FOL-name (allocated) to Item (allocated).
    struct HashTable *global_env;
    struct HashTable *local_env;

    // Maps source-code local name (shared with AST) to a "version number"
    // for that variable.
    struct HashTable *local_to_version;

    // Maps source-code local name (shared with AST) to the next valid
    // version-number for a variable with that name (as uintptr_t).
    // Cleared for each new Decl.
    struct HashTable *local_counter;

    // Used for string literals and fixed-sized-arrays
    struct HashTable *string_names;
    const char *current_decl_name;

    // Tracks references. Maps source-code local name (shared with
    // AST) to a RefChain struct (allocated).
    struct HashTable *refs;

    // Stack of ST_VAR_DECL variables.
    // (Both name and type are shared with AST.)
    struct NameTypeList *var_decl_stack;

    // Cached "new" values for postconditions
    struct HashTable *new_values;


    // A boolean expression that is true along the current code path.
    // For example, includes if-conditions or function preconditions.
    struct Sexpr *path_condition;

    // "Facts" are facts/theorems that have been proved as we go along
    // (for example, assert-statements).
    // Note facts usually take the form (=> path-condition something).
    struct Sexpr *facts;
    int num_facts;  // Cached length of the facts list


    // True if we are in interface-only mode. (Most verification checks
    // are skipped in this case.)
    bool interface_only;

    // Information for the current function, if applicable
    struct FunArg *function_args;
    struct Sexpr *arglist_sexpr;  // e.g. ((%x Int) (%y Int)). Could be NULL
    struct Sexpr *funapp_sexpr;   // e.g. (*f %x %y)  or just *f if no args

    // Postconditions, to be verified at a return statement
    struct Condition *postconds;

    // List of expressions currently being asserted/proved
    // (one per nested assert-stmt).
    // At "fix" statements the topmost assert_expr may be modified.
    struct Sexpr *assert_exprs;


    // Whether to print progress messages on stderr
    bool show_progress;

    // Debug and Cache files
    const char *debug_filename_prefix;
    struct HashTable *debug_files_created;
    struct CacheDb *cache_db;

    // Error and timeout handling
    int timeout_seconds;
    bool continue_after_error;
    bool error_found;


    // Hidden Names
    struct HashTable *local_hidden;
};

enum RefType {
    RT_LOCAL_VAR,
    RT_FIELD,
    RT_VARIANT,
    RT_ARRAY_ELEMENT,
    RT_ARRAY_CAST,
    RT_SEXPR    // used for const refs (e.g. ref x = "hello";)
};

struct RefChain {
    enum RefType ref_type;

    // For RT_LOCAL_VAR, RT_ARRAY_CAST or RT_SEXPR this contains the variable/ref type
    //  - shared with AST.
    // NULL for anything else.
    struct Type *type;

    // For RT_FIELD, RT_VARIANT or RT_ARRAY_ELEMENT, this contains the type of the
    // "lhs" (a record, variant or array type).
    // For RT_LOCAL_VAR, RT_ARRAY_CAST or RT_SEXPR this contains the type of the
    // reference itself.
    // Allocated on heap.
    struct Sexpr *fol_type;

    struct RefChain *base;     // allocated. NULL for RT_LOCAL_VAR or RT_SEXPR.
    union {
        struct {
            // Vars relevant to RT_LOCAL_VAR
            const char *variable_name;    // Shared with AST
            bool postcond_new;
        };
        struct {
            // Vars relevant to RT_FIELD and RT_VARIANT
            uint32_t index;  // Which field or variant
        };
        struct {
            // Vars relevant to RT_ARRAY_INDEX
            struct Sexpr *array_index;  // The index-expr
            int ndim;    // Number of dimensions of the array
            bool fixed_size;   // True if it is a fixed-size array
        };
        struct {
            // Vars relevant to RT_SEXPR
            struct Sexpr *sexpr;          // Allocated
        };
    };
};


//-------------------------------------------------------------------------------
// General helper functions
//-------------------------------------------------------------------------------

void free_conditions(struct Condition *cond);

void free_item(struct Item *item);
struct Item *copy_item(const struct Item *item);
void clear_verifier_env_hash_table(struct HashTable *table);

struct RefChain *copy_ref_chain(struct RefChain *);
void free_ref_chain(struct RefChain *);
void clear_refs_hash_table(struct HashTable *table);

// returns a statically-allocated string: "u32", "i64" etc.
// only works for TY_FINITE_INT types
const char *int_type_string(const struct Type *type);

// Make a new Item for a declare-const, and add it to the context
// (replacing an existing Item if there is one).
// Also returns a pointer to the Item.
struct Item *add_const_item(struct VContext *context,
                            const char *fol_name,    // Handed over
                            struct Type *type,  // Only needed if fol_term == NULL
                            struct Sexpr *fol_type,   // Handed over
                            struct Sexpr *fol_term,   // Handed over; can be NULL
                            bool local);

enum AllocFunc {
    ALLOC_ALWAYS,
    ALLOC_UNKNOWN,
    ALLOC_NEVER,
};

// add type variable(s) to the env (declare-sort)
// also add $default, $allocated and $valid items for each tyvar
struct Item * add_tyvar_to_env(struct VContext *context, const char *name, bool local,
                               enum AllocFunc alloc_func);
void add_tyvars_to_env(struct VContext *context, const struct TyVarList *tyvars);

// Remove an existing Item from the HashTable if there is one
void remove_existing_item(struct HashTable *table, const char *fol_name);

// Remove any facts mentioning a particular variable name.
void remove_facts(struct VContext *context, const char *fol_name);

// Add "instance" and tyargs to an expr, if required
void make_instance(struct Sexpr **expr,     // modified in place
                   struct Sexpr *tyargs);   // handed over

struct Sexpr *conjunction(struct Sexpr *expr_list);  // expr_list handed over
struct Sexpr *disjunction(struct Sexpr *expr_list);  // expr_list handed over

// return tester and selector functions for a given variant
void analyse_variant(const char *variant_name,
                     struct Type *type,
                     struct Type ** payload_type_out,  // will point to something in 'type'
                     struct Sexpr ** ctor_out,         // optional. will be allocated
                     struct Sexpr ** tester_out,       // will be allocated
                     struct Sexpr ** selector_out);    // optional. will be allocated

// Get modified vars taking into account references.
void get_modified_vars_deref(struct VContext *context,
                             struct HashTable *names,
                             struct Statement *stmt);

// return a new record which copies each of the fields of 'record'
struct Sexpr *copy_record_fields(struct Sexpr *record,       // shared (will be copied several times)
                                 struct Sexpr *field_types); // shared


// Returns "Int" if ndim=1, or a $PROD of Ints otherwise.
struct Sexpr * array_index_type(int ndim);

// Returns an expression saying that an array index is in range
// (checking both >= 0, and < size).
// If OpTermList given, entries will be checked to see if unsigned, in which case,
// the corresponding ">= 0" check can be skipped.
// If assume_nonneg is true, then ">= 0" check is always skipped.
struct Sexpr * array_index_in_range(int ndim, const char *idx_name, const char *size_name,
                                    const struct OpTermList *idx_terms,
                                    bool assume_nonneg);

// Produce an expression something like
//  forall $elt in $arr.
//    if $elt is in range for $arr then
//      expr
//    else
//      $elt == $ARBITRARY at elt_type.
// "expr" and "elt_type" are handed over.
// The variable $size, holding the array size, is assumed to exist.
struct Sexpr *for_all_array_elt(int ndim,
                                struct Sexpr *expr,
                                struct Sexpr *elt_type);

// create "match arr_expr with (arr_name,size_name) => rhs_expr"
// arr_expr, rhs_expr are handed over. arr_name, size_name are copied.
// array_type must be TY_ARRAY.
struct Sexpr *match_arr_size(const char *arr_name, const char *size_name,
                             struct Sexpr *arr_expr, struct Type *array_type,
                             struct Sexpr *rhs_expr);

// create a sexpr giving the size of a fixed-size array
// (i.e. where array_type->array_data.sizes != NULL).
struct Sexpr *fixed_arr_size_sexpr(struct Type *array_type);


//-------------------------------------------------------------------------------
// Fact and path condition helpers
//-------------------------------------------------------------------------------

// construct "(and lhs rhs)"; both inputs handed over
struct Sexpr *and_sexpr(struct Sexpr *lhs, struct Sexpr *rhs);

// construct "(and lhs (not rhs))"; both inputs handed over
struct Sexpr *and_not_sexpr(struct Sexpr *lhs, struct Sexpr *rhs);

// construct "(or lhs rhs)" (or an equivalent); both inputs handed over
struct Sexpr *or_sexpr(struct Sexpr *lhs, struct Sexpr *rhs);

// construct "(=> current-pc expr)"; expr handed over (context left unchanged)
struct Sexpr *pc_implies(struct VContext *context, struct Sexpr *expr);

// Construct (ite current-pc-expr expr NULL). (expr handed over.)
// The result is pasted in to **ret_val_ptr which should point to a NULL.
// Then *ret_val_ptr is moved to point to the new NULL (unless the ite was optimised away!).
void make_ite_pc_expr(struct Sexpr *** ret_val_ptr, struct VContext *context, struct Sexpr *expr);

// add (=> current-path-condition fact) to the list of currently known facts.
// 'fact' is handed over.
void add_fact(struct VContext *context, struct Sexpr *fact);

// get the number of currently known facts
int get_num_facts(struct VContext *context);

// delete facts, until get_num_facts is equal to the given num
void revert_facts(struct VContext *context, int num);



//-------------------------------------------------------------------------------
// Local variable helpers
//-------------------------------------------------------------------------------

// Update or add a local variable.
// Returns the new Item (which will have been added to cxt->env).
struct Item * update_local(struct VContext *context,
                           const char *local_name,     // Shared with AST
                           struct Type *type,       // Only needed if fol_term == NULL
                           struct Sexpr *fol_type,            // Handed over
                           struct Sexpr *fol_term);           // Handed over; can be NULL

// Same as update_local but does not add any definition to the env.
// Used in cases where a variable update failed to verify.
void poison_local(struct VContext *context,
                  const char *local_name);     // Shared with AST

// Lookup the current "FOL-name" of a local.
// Returns new allocated string (or NULL if not found).
// NOTE: Result might be poisoned, look in context->local_env to check.
char * lookup_local(struct VContext *context, const char *local_name);


//-------------------------------------------------------------------------------
// Functions for "snapshotting" the current version number of each
// source code variable
//-------------------------------------------------------------------------------

struct HashTable * snapshot_variable_versions(struct VContext *context,
                                              struct HashTable *modified_vars);

void revert_to_snapshot(struct VContext *context,
                        struct HashTable *snapshot);

void resolve_if_branches(struct VContext *context,
                         struct Sexpr *cond,    // shared
                         bool use_snapshot_when,
                         struct HashTable *snapshot);   // shared



//-------------------------------------------------------------------------------
// Functions for producing "validity conditions"
//-------------------------------------------------------------------------------

// returns an expression saying whether the given variable is valid
// e.g. ($in_range_i32 var_name)
// OR returns NULL if no checks are required for this type
struct Sexpr * validity_test_expr(struct Type *type, const char *var_name);

struct Sexpr * insert_validity_condition(struct VContext *context,
                                         enum Quantifier quant,
                                         struct Type *type,
                                         struct Sexpr *fol_var,
                                         struct Sexpr *term);

struct Sexpr * insert_validity_conditions(struct VContext *context,
                                          enum Quantifier quant,
                                          struct FunArg *fun_args,
                                          struct Sexpr *funapp_sexpr,
                                          struct Sexpr *term);


//-------------------------------------------------------------------------------
// "Allocated" predicate
//-------------------------------------------------------------------------------

// returns an expression saying whether the given variable is allocated,
// or NULL if it is always considered 'not allocated'
struct Sexpr * allocated_test_expr(struct Type *type, const char *var_name);

// return a condition that checks that the given term is NOT allocated,
// or NULL if no test is required
struct Sexpr * non_allocated_condition(struct VContext *context,
                                       struct Type *type,
                                       struct Sexpr *fol_term); // copied

#endif
