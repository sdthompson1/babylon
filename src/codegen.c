/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "codegen.h"
#include "error.h"
#include "hash_table.h"
#include "normal_form.h"
#include "opcode.h"
#include "size_expr.h"
#include "stack_machine.h"
#include "util.h"

#include <inttypes.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


//
// RefPath -- represents a reference
//

enum RefPathTag {
    REF_VAR,
    REF_STRING_LITERAL,
    REF_FIELD_PROJ,
    REF_DYNAMIC_ARRAY_PROJ,
    REF_FIXED_ARRAY_PROJ,
    REF_VARIANT_PAYLOAD
};

struct RefPath {
    enum RefPathTag tag;
    struct NameList *names;   // allocated
    struct Type *type;        // shared with AST. Type of the "result" of the lookup
    struct RefPath *parent;
};


//
// CodegenItem -- info about a source-level variable
//

enum CodegenType {
    CT_FUNCTION,
    CT_GLOBAL_VAR,
    CT_LOCAL_VAR,
    CT_POINTER_ARG,
    CT_REF
};


struct CodegenItem {
    enum CodegenType ctype;

    union {
        // For CT_REF, this gives the RefPath (allocated)
        struct RefPath *path;

        // For CT_FUNCTION, 'foreign_name' is the C name of this
        // function, if any (allocated).
        const char *foreign_name;
    };
};


// We need to keep track of scopes so that we know when to delete
// local vars from the stack-machine.
struct Scope {
    struct NameList *local_var_names;    // names are allocated
    struct Scope *next;
};


// String literals
struct StringLiteral {
    struct StringLiteral *next;
    const uint8_t *data;
    uint32_t length;
    const char *name;  // allocated
};


struct CGContext {
    struct StackMachine *machine;

    // codegen env
    // key = global or local name (allocated), value = CodegenItem (allocated)
    // exception: key "$StringNum" maps to a counter of string literals
    struct HashTable *env;

    // local scopes (linked list)
    struct Scope *scope;

    // temporary memory block counter
    int num_temps;

    // type variables of the current function, in order
    struct TyVarList *tyvars;

    // string literals to be created
    struct StringLiteral *strings;

    // counter for 'ref' variables
    int ref_counter;
};


static void free_ref_path(struct RefPath *path)
{
    while (path) {
        free_name_list(path->names);
        struct RefPath *to_free = path;
        path = path->parent;
        free(to_free);
    }
}

static char * mangle_name(const char *input)
{
    // Our decls have names like "M.x" where M is the module name and
    // x the function or const name.

    // For C compatibility we will change this into "M_x". This allows
    // the decls to be accessed from C if that is wanted.

    // Note that this system might produce duplicate definitions, e.g.
    // imagine two modules "Foo" and "Foo_bar", containing functions
    // "Foo.bar_baz" and "Foo_bar.baz" respectively. Both of these map
    // to "Foo_bar_baz". For now we will ignore this problem :)

    char *output = copy_string(input);
    for (char *p = output; *p; ++p) {
        if (*p == '.') *p = '_';
    }

    return output;
}

static bool is_memory_var_type(const struct Type *type)
{
    // We assume TY_VAR names containing a dot are global "abstract types"
    // i.e. "type Such_and_such;" at top level of the module.
    // Current we map these to a 64-bit integer value.

    // All other TY_VAR names are assumed to be local type variables
    // i.e. "function f<T>(...)".
    // These are considered to be a memory type, with the size being
    // passed to the function as a hidden parameter.

    return strchr(type->var_data.name, '.') == NULL;
}

static bool is_memory_type(const struct Type *type)
{
    return (type->tag == TY_VAR && is_memory_var_type(type))
        || type->tag == TY_RECORD
        || type->tag == TY_VARIANT
        || type->tag == TY_FIXED_ARRAY
        || type->tag == TY_DYNAMIC_ARRAY;
}

static bool is_signed_integral_type(const struct Type *type)
{
    if (type->tag == TY_FINITE_INT) {
        return type->int_data.is_signed;
    } else {
        return false;
    }
}

// calculate size of a TY_FINITE_INT or TY_BOOL type. Returns 1, 2, 4 or 8.
static int size_of_integral_type(const struct Type *type)
{
    if (type->tag == TY_FINITE_INT) {
        return type->int_data.num_bits / 8;
    } else if (type->tag == TY_BOOL) {
        return 1;
    } else if (type->tag == TY_VAR && strchr(type->var_data.name, '.') != NULL) {
        // see note in is_memory_var_type
        return 8;
    } else {
        fatal_error("not an integral type");
    }
}

static int type_or_pointer_size(const struct Type *type)
{
    if (is_memory_type(type)) {
        return 8;
    } else {
        return size_of_integral_type(type);
    }
}

// assumption: type is TY_VARIANT
static int get_tag_size(const struct Type *type)
{
    uint32_t num_tags = 0;
    for (struct NameTypeList *variant = type->variant_data.variants; variant; variant = variant->next) {
        ++num_tags;
        if (num_tags == 0) {
            fatal_error("too many variants");
        }
    }
    if (num_tags <= 256) {
        return 1;
    } else if (num_tags <= 65536) {
        return 2;
    } else {
        return 4;
    }
}

// assumption: type is TY_VARIANT, and given name is in the list
static uint32_t get_tag_number_and_payload_type(struct Type *type, const char *name, struct Type ** payload_type_out)
{
    uint32_t num = 0;
    for (struct NameTypeList *variant = type->variant_data.variants; variant; variant = variant->next) {
        if (strcmp(name, variant->name) == 0) {
            if (payload_type_out) {
                *payload_type_out = variant->type;
            }
            return num;
        }
        ++num;
        if (num == 0) {
            fatal_error("too many variants");
        }
    }
    fatal_error("variant tag not found");
}


// Calculate the size of a type, as a function of the sizes of
// the type variables currently in scope.
static struct SizeExpr * compute_size_of_type(struct StackMachine *mc,
                                              const struct Type *type)
{
    if (is_memory_type(type)) {

        if (type->tag == TY_RECORD) {
            // start with zero
            struct SizeExpr *output = zero_size_expr();

            for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
                // add size of each field
                struct SizeExpr *field_size = compute_size_of_type(mc, field->type);
                struct SizeExpr *new_size = add_size_expr(output, field_size);
                free_size_expr(output);
                free_size_expr(field_size);
                output = new_size;
            }

            return output;

        } else if (type->tag == TY_VARIANT) {
            struct SizeExpr *tag_size = const_size_expr(get_tag_size(type));
            struct SizeExpr *output = zero_size_expr();

            // The size is the max of the variant sizes,
            // where the size of each variant is the tag size plus the payload size.
            for (struct NameTypeList *variant = type->variant_data.variants; variant; variant = variant->next) {
                struct SizeExpr *payload_size = compute_size_of_type(mc, variant->type);
                struct SizeExpr *variant_size = add_size_expr(tag_size, payload_size);
                free_size_expr(payload_size);

                struct SizeExpr *new_size = max_size_expr(output, variant_size);
                free_size_expr(output);
                free_size_expr(variant_size);
                output = new_size;
            }

            free_size_expr(tag_size);
            return output;

        } else if (type->tag == TY_FIXED_ARRAY) {
            // A fixed array is just a block of memory of the correct size.
            struct SizeExpr *size = compute_size_of_type(mc, type->fixed_array_data.element_type);
            for (int i = 0; i < type->fixed_array_data.ndim; ++i) {
                uint64_t dim = normal_form_to_int(type->fixed_array_data.sizes[i]);
                struct SizeExpr *new_size = multiply_size_expr(dim, size);
                free_size_expr(size);
                size = new_size;
            }
            return size;

        } else if (type->tag == TY_DYNAMIC_ARRAY) {
            // A dynamic array is a pointer to the data followed by one 8-byte size per dimension.
            return const_size_expr(8 * (1 + type->dynamic_array_data.ndim));

        } else if (type->tag == TY_VAR) {
            // A type variable of the current function
            return var_size_expr(type->var_data.name, 1);

        } else {
            fatal_error("compute_size_of_type: unexpected case");
        }

    } else {
        return const_size_expr(size_of_integral_type(type));
    }
}

static void offset_pointer_by_size(struct StackMachine *mc, struct SizeExpr *size)
{
    if (!is_size_expr_zero(size)) {
        push_size_expr(mc, size);
        stk_alu(mc, OP_ADD);
    }
}


// Assuming two pointers are on the stack, do a memcpy of either a fixed or
// variable size as appropriate. (Source on top of stack, dest below.)
static void memcpy_type(struct StackMachine *mc, const struct Type *type)
{
    struct SizeExpr *size = compute_size_of_type(mc, type);

    if (is_size_expr_const(size)) {
        stk_memcpy_fixed_size(mc, get_size_expr_const(size));
    } else {
        push_size_expr(mc, size);
        stk_memcpy_variable_size(mc);
    }

    free_size_expr(size);
}

// Assuming a pointer is on the stack, do a memclear of either fixed or variable size as appropriate.
static void memclear_type(struct StackMachine *mc, const struct Type *type)
{
    struct SizeExpr *size = compute_size_of_type(mc, type);

    if (is_size_expr_const(size)) {
        stk_memclear_fixed_size(mc, get_size_expr_const(size));
    } else {
        push_size_expr(mc, size);
        stk_memclear_variable_size(mc);
    }

    free_size_expr(size);
}

static struct CGContext * new_cg_context(struct HashTable *env,
                                         struct StackMachine *mc,
                                         const char *fun_name)
{
    struct CGContext *cxt = alloc(sizeof(struct CGContext));
    cxt->machine = mc;
    cxt->env = env;
    cxt->scope = NULL;
    cxt->num_temps = 0;
    cxt->tyvars = NULL;
    cxt->strings = NULL;
    cxt->ref_counter = 0;

    stk_begin_function(mc, fun_name);

    return cxt;
}


static const char * add_string_literal(struct HashTable *env,
                                       struct StringLiteral **head_ptr,
                                       struct Term *term)
{
    uintptr_t num = (uintptr_t)hash_table_lookup(env, "$StringNum");
    ++num;
    hash_table_insert(env, "$StringNum", (void*)num);

    char name[50];
    sprintf(name, "string.%" PRIuPTR, num);

    struct StringLiteral *node = alloc(sizeof(struct StringLiteral));
    node->next = *head_ptr;
    node->data = term->string_literal.data;
    node->length = term->string_literal.length;
    node->name = copy_string(name);
    *head_ptr = node;

    return node->name;
}

static void write_string_descriptor(struct StackMachine *mc,
                                    struct StringLiteral *str)
{
    if (str->length == 0) {
        stk_insert_octa(mc, 0);
    } else {
        const char *data_name = copy_string_2(str->name, ".data");
        stk_insert_global_addr(mc, data_name);
        free((char*)data_name);
    }
    stk_insert_octa(mc, str->length);
}

// this creates each string literal and also frees the list
static void create_string_literals(struct StackMachine *mc,
                                   struct StringLiteral *str,
                                   bool write_descriptors)
{
    while (str) {

        if (write_descriptors) {
            stk_begin_global_constant(mc, str->name, str->length != 0, false);
            write_string_descriptor(mc, str);
            stk_end_global_constant(mc);
        }

        if (str->length != 0) {
            const char *data_name = copy_string_2(str->name, ".data");
            stk_begin_global_constant(mc, data_name, false, false);
            for (uint32_t i = 0; i < str->length; ++i) {
                stk_insert_byte(mc, str->data[i]);
            }
            stk_end_global_constant(mc);
            free((char*)data_name);
        }

        struct StringLiteral *next = str->next;
        free((char*)str->name);
        free(str);
        str = next;
    }
}

static void free_cg_context(struct CGContext *cxt)
{
    if (cxt->scope || cxt->num_temps != 0) {
        fatal_error("local scope or temporaries still exist");
    }
    stk_end_function(cxt->machine);
    free_tyvar_list(cxt->tyvars);
    create_string_literals(cxt->machine, cxt->strings, true);
    free(cxt);
}

// Open a new scope for local variables
static void push_local_scope(struct CGContext *context)
{
    struct Scope *scope = alloc(sizeof(struct Scope));
    scope->local_var_names = NULL;
    scope->next = context->scope;
    context->scope = scope;
}

// helper function
static void add_to_scope(struct CGContext *context,
                         const char *name,    // copied
                         enum CodegenType ctype,
                         struct RefPath *path)   // handed over
{
    struct NameList *node = alloc(sizeof(struct NameList));
    node->name = copy_string(name);
    node->next = context->scope->local_var_names;
    context->scope->local_var_names = node;

    struct CodegenItem *item = alloc(sizeof(struct CodegenItem));
    item->ctype = ctype;
    if (ctype == CT_REF) {
        item->path = path;
    } else if (ctype == CT_FUNCTION || path != NULL) {
        // 1) This function doesn't support adding CT_FUNCTION variables.
        // 2) If path != NULL then ctype should have been CT_REF.
        fatal_error("add_to_scope: incorrect arguments");
    }
    hash_table_insert(context->env, copy_string(name), item);
}


// Add a new local variable of the given size (must be 1/2/4/8 bytes)
static void add_new_local(struct CGContext *context,
                          const char *name,             // copied
                          bool is_signed,
                          int size)
{
    add_to_scope(context, name, CT_LOCAL_VAR, NULL);
    struct StackMachine *mc = context->machine;
    stk_create_local(mc, name, is_signed, size);
}

// Add a new local variable representing an area of stack memory.
static void add_named_mem_block(struct CGContext *context,
                                const char *name,
                                const struct Type *type)
{
    add_to_scope(context, name, CT_LOCAL_VAR, NULL);

    struct StackMachine *mc = context->machine;
    struct SizeExpr *size = compute_size_of_type(mc, type);

    if (is_size_expr_const(size)) {
        stk_create_mem_block_fixed_size(mc, name, get_size_expr_const(size));
    } else {
        push_size_expr(mc, size);
        stk_create_mem_block_variable_size(mc, name);
    }

    free_size_expr(size);
}

// Add a new reference variable
static void add_new_ref(struct CGContext *context,
                        const char *name,        // copied
                        struct RefPath *path)    // handed over
{
    add_to_scope(context, name, CT_REF, path);
}



// Temporary memory blocks
#define TEMP_NAME_SIZE 30

static void get_temp_block_name(struct CGContext *context, char buf[TEMP_NAME_SIZE])
{
    sprintf(buf, "!%d", context->num_temps++);
}

static void add_temp_mem_block(struct CGContext *context, const struct Type *type)
{
    char name[TEMP_NAME_SIZE];
    get_temp_block_name(context, name);
    add_named_mem_block(context, name, type);
}


static void free_codegen_item(void *context, const char *key, void *value);

// Remove one scope from context->scope, and remove all the locals of
// this scope from the machine.
static void pop_local_scope(struct CGContext *context)
{
    struct StackMachine *mc = context->machine;

    while (context->scope->local_var_names) {
        // look up in env
        const char *name = context->scope->local_var_names->name;

        const char *key;
        void *value;
        hash_table_lookup_2(context->env, name, &key, &value);

        if (key) {
            struct CodegenItem *item = value;

            // remove from machine if required
            switch (item->ctype) {
            case CT_FUNCTION:
            case CT_GLOBAL_VAR:
                break;

            case CT_LOCAL_VAR:
            case CT_POINTER_ARG:
                stk_destroy_local(mc, name);
                break;

            case CT_REF:
                // any array index variables are "owned" by the CT_REF and must
                // be removed now.
                for (struct RefPath *path = item->path; path; path = path->parent) {
                    if (path->tag == REF_DYNAMIC_ARRAY_PROJ || path->tag == REF_FIXED_ARRAY_PROJ) {
                        for (struct NameList *node = path->names; node; node = node->next) {
                            stk_destroy_local(mc, node->name);
                        }
                    }
                }
                break;
            }

            // remove from env
            hash_table_remove(context->env, name);
            free_codegen_item(NULL, key, item);
        }

        // remove from scope
        struct NameList *next = context->scope->local_var_names->next;
        free((void*)name);
        free(context->scope->local_var_names);
        context->scope->local_var_names = next;
    }

    // remove the scope itself
    struct Scope *next = context->scope->next;
    free(context->scope);
    context->scope = next;
}


// Remove all temp names/memory blocks
static void clean_up_temp_blocks(struct CGContext *context)
{
    int num_temps = context->num_temps;
    context->num_temps = 0;
    for (int i = 0; i < num_temps; ++i) {
        char name[TEMP_NAME_SIZE];
        get_temp_block_name(context, name);

        // remove from machine
        stk_destroy_local(context->machine, name);

        // remove from env
        const char *key;
        void *value;
        hash_table_lookup_2(context->env, name, &key, &value);
        hash_table_remove(context->env, name);
        free((void*)key);
        free(value);
    }
    context->num_temps = 0;
}

static struct Type * get_function_type(struct Term *term)
{
    struct Type *fun_type;
    if (term->call.func->tag == TM_TYAPP) {
        if (term->call.func->tyapp.lhs->type->tag != TY_FORALL) {
            fatal_error("get_function_type - function doesn't have FORALL type");
        }
        fun_type = term->call.func->tyapp.lhs->type->forall_data.type;
    } else {
        fun_type = term->call.func->type;
    }
    if (fun_type->tag != TY_FUNCTION) {
        fatal_error("get_function_type - function doesn't have FUNCTION type");
    }
    return fun_type;
}

// Given a local variable name, return the "underlying" variable name
// (i.e. chasing down any *direct* variable references) together
// with the corresponding CodegenItem.
static void look_up_local_variable(struct CGContext *context,
                                   const char *name_in,
                                   const char **name_out,
                                   struct CodegenItem **item_out)
{
    while (true) {
        struct CodegenItem *item = hash_table_lookup(context->env, name_in);
        if (!item) {
            fatal_error("look_up_local_variable: name not found");
        }

        if (item->ctype == CT_REF && item->path->tag == REF_VAR) {
            name_in = item->path->names->name;
        } else {
            if (item_out) *item_out = item;
            if (name_out) *name_out = name_in;
            return;
        }
    }
}


//
// Codegen pre-pass for terms. Does Sethi-Ullman numbering and
// allocates any required temporary memory blocks.
//

static void pre_codegen_term(struct CGContext *cxt, bool store, struct Term *term);

static bool arg_use_temp_block(struct CGContext *cxt, struct FunArg *formal, struct OpTermList *actual)
{
    // We need a temp mem block in the following cases:
    //  - When passing a scalar value (like "i32") to a pointer type (like "a"),
    //    NOT by reference.
    //  - When passing a scalar CT_LOCAL_VAR term by reference.

    if (is_memory_type(actual->rhs->type)) {
        return false;
    }

    if (is_memory_type(formal->type) && !formal->ref) {
        return true;
    }

    if (actual->rhs->tag == TM_VAR && formal->ref) {
        struct CodegenItem *item;
        look_up_local_variable(cxt, actual->rhs->var.name, NULL, &item);
        if (item->ctype == CT_LOCAL_VAR) {
            return true;
        }
    }

    return false;
}

static int pre_codegen_arguments(struct CGContext *cxt,
                                 struct FunArg *formal,
                                 struct OpTermList *actual)
{
    if (formal == NULL) {
        return 1;
    }

    int n = pre_codegen_arguments(cxt, formal->next, actual->next);

    bool use_temp_block = arg_use_temp_block(cxt, formal, actual);

    if (use_temp_block) {
        add_temp_mem_block(cxt, actual->rhs->type);
    }

    pre_codegen_term(cxt, use_temp_block, actual->rhs);

    // Sethi-Ullman number is the max of all the arguments
    if (actual->rhs->sethi_ullman_number > n) {
        n = actual->rhs->sethi_ullman_number;
    }

    return n;
}

static void pre_codegen_call(struct CGContext *cxt, bool store, struct Term *term)
{
    struct Type * fun_type = get_function_type(term);

    // "struct" returns go to a temporary buffer
    if (term->type && is_memory_type(fun_type->function_data.return_type)) {
        add_temp_mem_block(cxt, term->type);
    }

    // check the arguments (in right-to-left order)
    term->sethi_ullman_number =
        pre_codegen_arguments(cxt, fun_type->function_data.args, term->call.args);
}

static void pre_codegen_term(struct CGContext *cxt, bool store, struct Term *term)
{
    switch (term->tag) {
    case TM_VAR:
    case TM_BOOL_LITERAL:
    case TM_INT_LITERAL:
    case TM_STRING_LITERAL:
        term->sethi_ullman_number = 1;
        break;

    case TM_DEFAULT:
    case TM_MATCH_FAILURE:
        if (!store && is_memory_type(term->type)) {
            add_temp_mem_block(cxt, term->type);
        }
        term->sethi_ullman_number = 1;
        break;

    case TM_CAST:
        pre_codegen_term(cxt, false, term->cast.operand);
        term->sethi_ullman_number = term->cast.operand->sethi_ullman_number;
        break;

    case TM_IF:
        pre_codegen_term(cxt, false, term->if_data.cond);
        pre_codegen_term(cxt, store, term->if_data.then_branch);
        pre_codegen_term(cxt, store, term->if_data.else_branch);
        {
            int n = term->if_data.cond->sethi_ullman_number;
            int n2 = term->if_data.then_branch->sethi_ullman_number;
            int n3 = term->if_data.else_branch->sethi_ullman_number;
            if (n2 > n) n = n2;
            if (n3 > n) n = n3;
            term->sethi_ullman_number = n;
        }
        break;

    case TM_UNOP:
        pre_codegen_term(cxt, false, term->unop.operand);
        term->sethi_ullman_number = term->unop.operand->sethi_ullman_number;
        break;

    case TM_BINOP:
        {
            enum BinOp binop = term->binop.list->operator;
            bool lhs_store = false;
            bool rhs_store = false;
            if (binop == BINOP_AND || binop == BINOP_OR || binop == BINOP_IMPLIES) {
                rhs_store = store;
            }
            pre_codegen_term(cxt, lhs_store, term->binop.lhs);
            pre_codegen_term(cxt, rhs_store, term->binop.list->rhs);

            int n1 = term->binop.lhs->sethi_ullman_number;
            int n2 = term->binop.list->rhs->sethi_ullman_number;
            int n;
            if (n1 > n2) {
                n = n1;
            } else if (n2 > n1) {
                n = n2;
            } else {
                n = n1 + 1;
            }
            term->sethi_ullman_number = n;
        }
        break;

    case TM_LET:
        pre_codegen_term(cxt, false, term->let.rhs);
        pre_codegen_term(cxt, store, term->let.body);
        {
            int n1 = term->let.rhs->sethi_ullman_number;
            int n2 = term->let.body->sethi_ullman_number;
            term->sethi_ullman_number = (n1 > n2 ? n1 : n2);
        }
        break;

    case TM_QUANTIFIER:
        fatal_error("pre_codegen_term: trying to codegen TM_QUANTIFIER");

    case TM_CALL:
        pre_codegen_call(cxt, store, term);
        break;

    case TM_TYAPP:
        fatal_error("pre_codegen_term: trying to codegen TM_TYAPP");

    case TM_RECORD:
        if (!store) {
            add_temp_mem_block(cxt, term->type);
        }
        {
            int n = 1;
            for (struct NameTermList *field = term->record.fields; field; field = field->next) {
                pre_codegen_term(cxt, true, field->term);
                if (field->term->sethi_ullman_number > n) {
                    n = field->term->sethi_ullman_number;
                }
            }
            term->sethi_ullman_number = n;
        }
        break;

    case TM_RECORD_UPDATE:
        if (!store) {
            add_temp_mem_block(cxt, term->type);
        }
        {
            pre_codegen_term(cxt, true, term->record_update.lhs);
            int n = term->record_update.lhs->sethi_ullman_number;
            for (struct NameTermList *field = term->record_update.fields; field; field = field->next) {
                pre_codegen_term(cxt, true, field->term);
                if (field->term->sethi_ullman_number > n) {
                    n = field->term->sethi_ullman_number;
                }
            }
            term->sethi_ullman_number = n;
        }
        break;

    case TM_FIELD_PROJ:
        pre_codegen_term(cxt, false, term->field_proj.lhs);
        term->sethi_ullman_number = term->field_proj.lhs->sethi_ullman_number;
        break;

    case TM_VARIANT:
        if (!store) {
            add_temp_mem_block(cxt, term->type);
        }
        pre_codegen_term(cxt, true, term->variant.payload);
        term->sethi_ullman_number = term->variant.payload->sethi_ullman_number;
        break;

    case TM_MATCH:
        {
            pre_codegen_term(cxt, false, term->match.scrutinee);
            int n = term->match.scrutinee->sethi_ullman_number;
            for (struct Arm *arm = term->match.arms; arm; arm = arm->next) {
                pre_codegen_term(cxt, store, arm->rhs);
                int n2 = ((struct Term*)arm->rhs)->sethi_ullman_number;
                if (n2 > n) {
                    n = n2;
                }
            }
            term->sethi_ullman_number = n;
        }
        break;

    case TM_SIZEOF:
        {
            struct Term *rhs = term->sizeof_data.rhs;
            int ndim = array_ndim(rhs->type);
            if (!store && ndim > 1) {
                add_temp_mem_block(cxt, term->type);
            }
            pre_codegen_term(cxt, false, rhs);
            term->sethi_ullman_number = rhs->sethi_ullman_number;
        }
        break;

    case TM_ALLOCATED:
        fatal_error("pre_codegen_term: trying to codegen TM_ALLOCATED");

    case TM_ARRAY_PROJ:
        {
            pre_codegen_term(cxt, false, term->array_proj.lhs);
            int n = term->array_proj.lhs->sethi_ullman_number;
            for (struct OpTermList *node = term->array_proj.indexes; node; node = node->next) {
                pre_codegen_term(cxt, false, node->rhs);
                if (node->rhs->sethi_ullman_number > n) {
                    n = node->rhs->sethi_ullman_number;
                }
            }
            term->sethi_ullman_number = n;
        }
        break;
    }
}



//
// Code generation for terms
//

enum CodegenMode {
    PUSH_VALUE,
    PUSH_ADDR,
    STORE_TO_MEM
};

// Evaluate the given term, according to 'mode'.

// Mode PUSH_VALUE pushes the value of the term to the stack.
// The value must be a scalar type (bool or integer).

// Mode PUSH_ADDR pushes the *address* of the value to the stack.
// If the term is an lvalue, this looks up the existing addr (if
// possible). For rvalues a temporary block is filled and the addr
// of the temporary block is returned.

// Mode STORE_TO_MEM computes the term into the address currently on
// top of stack. This addr is popped afterwards. (This works with all
// kinds of term whether they fit into a register or not.)

// Special case: if generating a TM_CALL that doesn't return
// a value, then 'mode' is ignored.

static void codegen_term(struct CGContext *cxt,
                         enum CodegenMode mode,
                         struct Term *term);

static void push_ref_addr(struct CGContext *context,
                          struct RefPath *path);

static struct RefPath * codegen_ref(struct CGContext *cxt,
                                    struct Term *term);

static void codegen_statements(struct CGContext *context, struct Statement *stmts);

static void codegen_var(struct CGContext *cxt,
                        enum CodegenMode mode,
                        const char *name_in,
                        struct Type *type)
{
    struct StackMachine *mc = cxt->machine;

    const char *name;
    struct CodegenItem *item;
    look_up_local_variable(cxt, name_in, &name, &item);

    switch (item->ctype) {
    case CT_GLOBAL_VAR:
        ;
        char *mangled_name = mangle_name(name);

        switch (mode) {
        case PUSH_ADDR:
            // push addr of global
            stk_push_global_addr(mc, mangled_name);
            break;

        case PUSH_VALUE:
        case STORE_TO_MEM:
            if (is_memory_type(type)) {
                if (mode == STORE_TO_MEM) {
                    // memcpy global
                    stk_push_global_addr(mc, mangled_name);
                    memcpy_type(mc, type);
                } else {
                    fatal_error("can't use PUSH_VALUE with memory type");
                }
            } else {
                // first put the value on the stack
                stk_push_global_value(mc,
                                      mangled_name,
                                      is_signed_integral_type(type),
                                      size_of_integral_type(type));

                // now store to memory if required
                if (mode == STORE_TO_MEM) {
                    stk_store(mc, size_of_integral_type(type));
                }
            }
            break;
        }
        free(mangled_name);
        break;

    case CT_LOCAL_VAR:
        // Local variable. Get its value on stack.
        stk_get_local(mc, name);

        if (is_memory_type(type)) {
            // We have pushed an address
            switch (mode) {
            case PUSH_ADDR:
                // Nothing else required
                break;

            case STORE_TO_MEM:
                // Memcpy the value into position
                memcpy_type(mc, type);
                break;

            case PUSH_VALUE:
                fatal_error("can't push value of a memory type");
            }

        } else {
            // We have pushed a value
            switch (mode) {
            case PUSH_ADDR:
                fatal_error("can't take addr of this variable");

            case PUSH_VALUE:
                // Nothing else required
                break;

            case STORE_TO_MEM:
                // Store the value
                stk_store(mc, size_of_integral_type(type));
                break;
            }
        }
        break;

    case CT_REF:
    case CT_POINTER_ARG:
        // Push the referenced address
        if (item->ctype == CT_REF) {
            push_ref_addr(cxt, item->path);
        } else {
            stk_get_local(mc, name);
        }

        switch (mode) {
        case PUSH_ADDR:
            // Nothing else required
            break;

        case PUSH_VALUE:
            // Load the value
            stk_load(mc, is_signed_integral_type(type), size_of_integral_type(type));
            break;

        case STORE_TO_MEM:
            // Memcpy the value
            memcpy_type(mc, type);
            break;
        }
        break;

    case CT_FUNCTION:
        fatal_error("unexpected ctype");
    }
}

static void codegen_default(struct CGContext *cxt, enum CodegenMode mode, struct Type *type)
{
    struct StackMachine *mc = cxt->machine;

    if (is_memory_type(type)) {
        switch (mode) {
        case STORE_TO_MEM:
            memclear_type(mc, type);
            break;

        case PUSH_VALUE:
            fatal_error("can't use PUSH_VALUE with memory type");

        case PUSH_ADDR:
            ;
            // get address of temp block
            char name[TEMP_NAME_SIZE];
            get_temp_block_name(cxt, name);
            stk_get_local(mc, name);

            // clear the temp block
            memclear_type(mc, type);

            // get address of temp block again
            stk_get_local(mc, name);
        }

    } else {
        switch (mode) {
        case PUSH_VALUE:
        case STORE_TO_MEM:
            stk_const(mc, 0);
            if (mode == STORE_TO_MEM) {
                stk_store(mc, size_of_integral_type(type));
            }
            break;

        case PUSH_ADDR:
            fatal_error("can't take addr of TM_DEFAULT of non-memory type");
        }
    }
}

static void codegen_bool_literal(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    if (mode == PUSH_ADDR) {
        fatal_error("can't take addr of literal");
    }

    struct StackMachine *mc = cxt->machine;
    stk_const(mc, term->bool_literal.value ? 1 : 0);

    if (mode == STORE_TO_MEM) {
        stk_store(cxt->machine, size_of_integral_type(term->type));
    }
}

static void codegen_int_literal(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    if (mode == PUSH_ADDR) {
        fatal_error("can't take addr of literal");
    }

    uint64_t value = parse_int_literal(term->int_literal.data);

    struct StackMachine *mc = cxt->machine;
    stk_const(mc, value);

    if (mode == STORE_TO_MEM) {
        stk_store(cxt->machine, size_of_integral_type(term->type));
    }
}

static void codegen_string_literal(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    add_string_literal(cxt->env, &cxt->strings, term);
    stk_push_global_addr(cxt->machine, cxt->strings->name);

    switch (mode) {
    case PUSH_VALUE:
        fatal_error("can't push a string constant");

    case PUSH_ADDR:
        // Nothing else required
        break;

    case STORE_TO_MEM:
        memcpy_type(cxt->machine, term->type);
        break;
    }
}

static void codegen_cast(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    if (mode == PUSH_ADDR) {
        fatal_error("can't take addr of cast");
    }

    // Push the operand to the stack.
    codegen_term(cxt, PUSH_VALUE, term->cast.operand);

    // Store to destination if we have been asked to do so.
    if (mode == STORE_TO_MEM) {
        stk_store(cxt->machine, size_of_integral_type(term->type));
    }
}

static void codegen_if(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    struct StackMachine *mc = cxt->machine;

    codegen_term(cxt, PUSH_VALUE, term->if_data.cond);
    stk_cond_if_nonzero(mc, 1);

    codegen_term(cxt, mode, term->if_data.then_branch);
    stk_cond_else(mc);

    codegen_term(cxt, mode, term->if_data.else_branch);
    stk_cond_endif(mc);
}

static void codegen_unop(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    if (mode == PUSH_ADDR) {
        fatal_error("can't take addr of unop");
    }

    codegen_term(cxt, PUSH_VALUE, term->unop.operand);

    enum Opcode op = OP_ADD;  // dummy value
    switch (term->unop.operator) {
    case UNOP_NEGATE: op = OP_NEG; break;
    case UNOP_COMPLEMENT: op = OP_NOT; break;
    case UNOP_NOT: op = OP_XOR_1; break;
    }
    if (op == OP_ADD) {
        fatal_error("unknown unop");
    }

    struct StackMachine *mc = cxt->machine;
    stk_alu(mc, op);

    if (mode == STORE_TO_MEM) {
        stk_store(mc, size_of_integral_type(term->type));
    }
}

static void codegen_binop(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    if (mode == PUSH_ADDR) {
        fatal_error("can't take addr of binop");
    }

    struct StackMachine *mc = cxt->machine;

    enum BinOp binop = term->binop.list->operator;

    if (binop == BINOP_AND || binop == BINOP_OR || binop == BINOP_IMPLIES) {
        // Short-circuit operator

        // AND:     if (lhs) rhs else false
        // OR:      if (lhs) true else rhs
        // IMPLIES: if (lhs) rhs else true

        codegen_term(cxt, PUSH_VALUE, term->binop.lhs);
        stk_cond_if_nonzero(mc, 1);

        switch (binop) {
        case BINOP_AND:
            codegen_term(cxt, mode, term->binop.list->rhs);
            stk_cond_else(mc);
            stk_const(mc, 0);
            if (mode == STORE_TO_MEM) {
                stk_store(mc, size_of_integral_type(term->type));
            }
            break;

        case BINOP_OR:
            stk_const(mc, 1);
            if (mode == STORE_TO_MEM) {
                stk_store(mc, size_of_integral_type(term->type));
            }
            stk_cond_else(mc);
            codegen_term(cxt, mode, term->binop.list->rhs);
            break;

        default:
            // BINOP_IMPLIES
            codegen_term(cxt, mode, term->binop.list->rhs);
            stk_cond_else(mc);
            stk_const(mc, 1);
            if (mode == STORE_TO_MEM) {
                stk_store(mc, size_of_integral_type(term->type));
            }
            break;
        }

        stk_cond_endif(mc);

    } else {
        // Normal binop, where both operands need to be evaluated

        // Recursively codegen the two sub-terms -- highest Sethi-Ullman number first.
        bool left_first = false;
        if (term->binop.lhs->sethi_ullman_number >= term->binop.list->rhs->sethi_ullman_number) {
            left_first = true;
        }

        if (left_first) {
            codegen_term(cxt, PUSH_VALUE, term->binop.lhs);
            codegen_term(cxt, PUSH_VALUE, term->binop.list->rhs);
        } else {
            codegen_term(cxt, PUSH_VALUE, term->binop.list->rhs);
            codegen_term(cxt, PUSH_VALUE, term->binop.lhs);
            stk_swap(mc, 0, 1);  // RHS needs to be on top of stack
        }

        bool is_signed = false;
        if (term->binop.lhs->type->tag == TY_FINITE_INT) {
            is_signed = term->binop.lhs->type->int_data.is_signed;
        }

        enum Opcode op = OP_NEG;  // dummy value
        switch (binop) {
        case BINOP_PLUS: op = OP_ADD; break;
        case BINOP_MINUS: op = OP_SUB; break;
        case BINOP_TIMES: op = OP_MUL; break;
        case BINOP_DIVIDE: op = is_signed ? OP_SDIV : OP_UDIV; break;
        case BINOP_MODULO: op = is_signed ? OP_SREM : OP_UREM; break;
        case BINOP_BITAND: op = OP_AND; break;
        case BINOP_BITOR: op = OP_OR; break;
        case BINOP_BITXOR: op = OP_XOR; break;
        case BINOP_SHIFTLEFT: op = OP_SHL; break;
        case BINOP_SHIFTRIGHT: op = is_signed ? OP_ASR : OP_LSR; break;
        case BINOP_EQUAL: op = OP_EQ; break;
        case BINOP_NOT_EQUAL: op = OP_NE; break;
        case BINOP_LESS: op = is_signed ? OP_SLT : OP_ULT; break;
        case BINOP_LESS_EQUAL: op = is_signed ? OP_SLE : OP_ULE; break;
        case BINOP_GREATER: op = is_signed ? OP_SGT : OP_UGT; break;
        case BINOP_GREATER_EQUAL: op = is_signed ? OP_SGE : OP_UGE; break;
        case BINOP_IFF: op = OP_EQ; break;
        case BINOP_AND: case BINOP_OR: case BINOP_IMPLIES: fatal_error("unreachable");
        case BINOP_IMPLIED_BY: fatal_error("<== is removed by typechecker");
        }
        if (op == OP_NEG) {
            fatal_error("unknown binop");
        }

        // Do the computation -- pops 2 operands and pushes result.
        stk_alu(mc, op);

        // Store to destination address if required
        if (mode == STORE_TO_MEM) {
            stk_store(mc, size_of_integral_type(term->type));
        }
    }
}

static void codegen_let(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    struct StackMachine *mc = cxt->machine;

    const struct Type *rhs_type = term->let.rhs->type;
    bool is_signed = is_signed_integral_type(rhs_type);
    int rhs_size = type_or_pointer_size(rhs_type);

    enum CodegenMode rhs_mode = is_memory_type(term->let.rhs->type) ? PUSH_ADDR : PUSH_VALUE;
    codegen_term(cxt, rhs_mode, term->let.rhs);

    push_local_scope(cxt);

    add_new_local(cxt, term->let.name, is_signed, rhs_size);
    stk_set_local(mc, term->let.name);

    codegen_term(cxt, mode, term->let.body);

    pop_local_scope(cxt);
}


// Pass all actual function arguments in right-to-left order.
// returns a list indicating the temp blocks used for each argument, if any.
static struct NameList * pass_actual_arguments(struct CGContext *cxt,
                                               struct FunArg *formal,
                                               struct OpTermList *actual)
{
    if (!formal) return NULL;

    struct StackMachine *mc = cxt->machine;

    // This recursion will traverse the list in reverse order.
    // Because we don't expect thousands of function arguments, recursion should be OK here.
    struct NameList *old_name_list = pass_actual_arguments(cxt, formal->next, actual->next);

    struct NameList *new_name_list = alloc(sizeof(struct NameList));
    new_name_list->name = NULL;
    new_name_list->next = old_name_list;

    bool use_temp_block = arg_use_temp_block(cxt, formal, actual);

    // If appropriate, just directly compute the addr of the argument
    // term onto the stack
    if (!use_temp_block &&
    (is_memory_type(formal->type) || formal->ref)) {
        codegen_term(cxt, PUSH_ADDR, actual->rhs);

    } else {
        // If we are using a temp block then get the addr of the temp
        // block onto the stack
        char name[TEMP_NAME_SIZE];
        if (use_temp_block) {
            get_temp_block_name(cxt, name);
            new_name_list->name = copy_string(name);
            stk_get_local(mc, name);
        }

        // Push the value of the argument onto the stack, OR copy its
        // value to the temp block
        codegen_term(cxt, use_temp_block ? STORE_TO_MEM : PUSH_VALUE, actual->rhs);

        // If we're using a temp block then put its address on the
        // stack once more
        if (use_temp_block) {
            stk_get_local(mc, name);
        }
    }

    // Pass the argument.
    stk_load_function_argument(mc);

    return new_name_list;
}

// Pass the hidden size arguments in right-to-left order.
static void pass_size_arguments(struct CGContext *cxt, struct TypeList *tyarg)
{
    if (!tyarg) return;

    pass_size_arguments(cxt, tyarg->next);

    struct StackMachine *mc = cxt->machine;
    struct SizeExpr *size = compute_size_of_type(mc, tyarg->type);
    push_size_expr(mc, size);
    free_size_expr(size);
    stk_load_function_argument(mc);
}

static void codegen_call(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    struct StackMachine *mc = cxt->machine;

    struct Type * fun_type = get_function_type(term);

    // Calculate the total number of arguments
    int num_args = 0;
    if (term->type && is_memory_type(fun_type->function_data.return_type)) {
        ++num_args;
    }
    if (term->call.func->tag == TM_TYAPP) {
        for (struct TypeList *tyarg = term->call.func->tyapp.tyargs; tyarg; tyarg = tyarg->next) {
            ++num_args;
        }
    }
    for (struct OpTermList *arg = term->call.args; arg; arg = arg->next) {
        ++num_args;
    }

    stk_prepare_function_call(mc, num_args);

    // Pass the arguments to the function, in right-to-left order
    struct NameList *temps = pass_actual_arguments(cxt, fun_type->function_data.args, term->call.args);

    // Pass the hidden size arguments, in right-to-left order, if applicable
    if (term->call.func->tag == TM_TYAPP) {
        pass_size_arguments(cxt, term->call.func->tyapp.tyargs);
    }

    // Figure out what we're doing with the return value
    bool returns_value = false;
    char return_temporary[TEMP_NAME_SIZE];
    return_temporary[0] = 0;
    if (term->type) {
        if (is_memory_type(fun_type->function_data.return_type)) {
            // The callee is returning a struct (or generic value).
            // Write this to a temporary block.
            get_temp_block_name(cxt, return_temporary);
            stk_get_local(mc, return_temporary);
            stk_load_function_argument(mc);

        } else {
            // The callee is returning a simple scalar value (e.g. i32),
            // so we can use the StackMachine's return mechanism for that.
            returns_value = true;
        }
    }

    // Make the call
    const char *fun_name;
    if (term->call.func->tag == TM_VAR) {
        fun_name = term->call.func->var.name;
    } else if (term->call.func->tag == TM_TYAPP
               && term->call.func->tyapp.lhs->tag == TM_VAR) {
        fun_name = term->call.func->tyapp.lhs->var.name;
    } else {
        fatal_error("codegen_call - couldn't obtain function name");
    }

    // sanity check
    struct CodegenItem *item = hash_table_lookup(cxt->env, fun_name);
    if (item == NULL || item->ctype != CT_FUNCTION) {
        fatal_error("codegen_call - failed to find function in the env (or it had wrong type)");
    }

    if (item->foreign_name) {
        // "foreign_name" is unmangled
        stk_emit_function_call(mc, item->foreign_name, returns_value);
    } else {
        // "fun_name" needs to be mangled
        char *new_name = mangle_name(fun_name);
        stk_emit_function_call(mc, new_name, returns_value);
        free(new_name);
    }

    // If we told the function to return to a temporary block then we
    // need to sort that out now.
    if (return_temporary[0] != 0) {
        // Put the pointer to the temporary return block on the stack.
        stk_get_local(mc, return_temporary);

        if (!is_memory_type(term->type)) {
            // This is the case where the function returns a generic value,
            // but we are expecting (on our side) something like i32.
            // Solve this by doing a "load".
            stk_load(mc, is_signed_integral_type(term->type), size_of_integral_type(term->type));
        }
    }

    // Copy ref local variables back if required
    struct NameList *temp = temps;
    struct FunArg *formal;
    struct OpTermList *actual;
    for (formal = fun_type->function_data.args, actual = term->call.args;
    actual;
    formal = formal->next, actual = actual->next, temp = temp->next) {
        if (formal->ref && temp->name) {
            // push addr of temp block
            stk_get_local(mc, temp->name);

            // load scalar value from temp block
            stk_load(mc,
                     is_signed_integral_type(actual->rhs->type),
                     size_of_integral_type(actual->rhs->type));

            if (actual->rhs->tag != TM_VAR) {
                fatal_error("inconsistency - argument should be a local variable in this case");
            }

            const char *name;
            struct CodegenItem *item;
            look_up_local_variable(cxt, actual->rhs->var.name, &name, &item);

            if (item->ctype != CT_LOCAL_VAR) {
                fatal_error("inconsistency - was expecting CT_LOCAL_VAR here");
            }

            // save the new value into the local
            stk_set_local(mc, name);
        }
    }

    free_name_list(temps);

    // Store, if requested by our caller, and if the function returned
    // something to store.
    if (term->type) {
        if (is_memory_type(term->type)) {
            switch (mode) {
            case PUSH_ADDR:
                // Nothing else needed. Return addr is on top of stack.
                break;

            case PUSH_VALUE:
                fatal_error("can't use PUSH_VALUE with memory type");

            case STORE_TO_MEM:
                memcpy_type(mc, term->type);
                break;
            }
        } else {
            switch (mode) {
            case PUSH_ADDR:
                fatal_error("can't take addr of TM_CALL where return value is not a memory type");

            case PUSH_VALUE:
                // Nothing else needed. Return value is on top of stack.
                break;

            case STORE_TO_MEM:
                stk_store(mc, size_of_integral_type(term->type));
                break;
            }
        }
    }
}

static void codegen_record(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    if (mode == PUSH_VALUE) {
        fatal_error("can't use PUSH_VALUE with TM_RECORD");
    }

    struct StackMachine *mc = cxt->machine;

    char name[TEMP_NAME_SIZE];
    if (mode == PUSH_ADDR) {
        // PUSH_ADDR mode needs a temp block
        get_temp_block_name(cxt, name);
        stk_get_local(mc, name);
    }

    for (struct NameTermList *field = term->record.fields; field; field = field->next) {
        // calculate size of this field
        struct SizeExpr *size = compute_size_of_type(mc, field->term->type);

        // if there is another field after this one, then we will
        // still need the pointer, so duplicate it
        if (field->next) {
            stk_dup(mc, 0);
        }

        // evaluate the initialiser, storing it to the pointer
        codegen_term(cxt, STORE_TO_MEM, field->term);

        // if there is another field after this one, then advance the
        // pointer to the next field (by adding current field's size)
        if (field->next) {
            offset_pointer_by_size(mc, size);
        }

        free_size_expr(size);
    }

    if (mode == STORE_TO_MEM && term->record.fields == NULL) {
        // There was nothing to store so pop the caller's store-ptr.
        stk_pop(mc);
    }

    if (mode == PUSH_ADDR && term->record.fields != NULL) {
        // Get the pointer back onto the stack
        stk_get_local(mc, name);
    }
}

static void codegen_record_update(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    if (mode == PUSH_VALUE) {
        fatal_error("can't use PUSH_VALUE with TM_RECORD_UPDATE");
    }

    struct StackMachine *mc = cxt->machine;

    char name[TEMP_NAME_SIZE];
    if (mode == PUSH_ADDR) {
        // PUSH_ADDR mode needs a temp block
        get_temp_block_name(cxt, name);
        stk_get_local(mc, name);
    }

    // Generate the "base" record term
    // (keeping the pointer on the stack!)
    stk_dup(mc, 0);
    codegen_term(cxt, STORE_TO_MEM, term->record_update.lhs);

    struct SizeExpr *offset_from_prev_update = zero_size_expr();

    for (struct NameTypeList *node = term->type->record_data.fields; node; node = node->next) {

        // see if there is an update for this field
        struct NameTermList *update;
        for (update = term->record_update.fields; update; update = update->next) {
            if (strcmp(update->name, node->name) == 0) {
                break;
            }
        }

        if (update) {
            // Advance the pointer by the required amount
            offset_pointer_by_size(mc, offset_from_prev_update);
            free_size_expr(offset_from_prev_update);
            offset_from_prev_update = zero_size_expr();

            // Generate the updated field, overwriting the previous
            // contents.
            stk_dup(mc, 0);
            codegen_term(cxt, STORE_TO_MEM, update->term);
        }

        // Work out how much we need to advance the pointer by
        // to skip over this field.
        struct SizeExpr *field_size = compute_size_of_type(mc, node->type);
        struct SizeExpr *total = add_size_expr(offset_from_prev_update, field_size);
        free_size_expr(field_size);
        free_size_expr(offset_from_prev_update);
        offset_from_prev_update = total;
    }

    free_size_expr(offset_from_prev_update);

    // Get rid of the (now "moved up") pointer from the stack.
    stk_pop(mc);

    // In PUSH_ADDR mode we need the original pointer back again.
    if (mode == PUSH_ADDR) {
        stk_get_local(mc, name);
    }
}

static void offset_for_field_proj(struct StackMachine *mc, struct Type *type, const char *field_name)
{
    // Work out how much to offset the pointer by
    struct SizeExpr *total_size = zero_size_expr();

    for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
        struct SizeExpr *field_size = compute_size_of_type(mc, field->type);

        if (strcmp(field->name, field_name) == 0) {
            free_size_expr(field_size);

            // Displace the pointer by the required amount
            offset_pointer_by_size(mc, total_size);

            free_size_expr(total_size);
            return;
        }

        struct SizeExpr *new_size = add_size_expr(total_size, field_size);
        free_size_expr(field_size);
        free_size_expr(total_size);
        total_size = new_size;
    }

    fatal_error("field not found");
}

static void codegen_field_proj(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    struct StackMachine *mc = cxt->machine;

    // Put the address of the record on top of the stack
    codegen_term(cxt, PUSH_ADDR, term->field_proj.lhs);

    // Offset by the required amount
    offset_for_field_proj(mc, term->field_proj.lhs->type, term->field_proj.field_name);

    // Do a load if required (otherwise just leave the pointer on stack)
    switch (mode) {
    case PUSH_ADDR:
        // Nothing required
        break;

    case PUSH_VALUE:
        // Load value, pop the pointer
        if (is_memory_type(term->type)) {
            fatal_error("can't use PUSH_VALUE with memory type");
        }
        stk_load(mc, is_signed_integral_type(term->type), size_of_integral_type(term->type));
        break;

    case STORE_TO_MEM:
        // Memcpy and pop both pointers
        memcpy_type(mc, term->type);
        break;
    }
}

static void codegen_variant(struct CGContext *cxt, enum CodegenMode mode, struct Term *term)
{
    if (mode == PUSH_VALUE) {
        fatal_error("can't use PUSH_VALUE with TM_VARIANT");
    }

    struct StackMachine *mc = cxt->machine;

    char name[TEMP_NAME_SIZE];
    if (mode == PUSH_ADDR) {
        // PUSH_ADDR mode needs a temp block
        get_temp_block_name(cxt, name);
        stk_get_local(mc, name);
    }

    // write the tag
    stk_dup(mc, 0);
    uint32_t tag_num = get_tag_number_and_payload_type(term->type, term->variant.variant_name, NULL);
    stk_const(mc, tag_num);
    stk_store(mc, get_tag_size(term->type));

    // place the payload after the tag
    stk_const(mc, get_tag_size(term->type));
    stk_alu(mc, OP_ADD);

    // codegen the payload, placing it in the computed position
    codegen_term(cxt, STORE_TO_MEM, term->variant.payload);

    if (mode == PUSH_ADDR) {
        // Get the pointer back onto the stack
        stk_get_local(mc, name);
    }
}

static char* next_ref_name(struct CGContext *cxt)
{
    if (cxt->ref_counter == INT_MAX) {
        fatal_error("ref_counter overflow");
    }
    char name[40];
    sprintf(name, "$Ref:%d", cxt->ref_counter++);
    return copy_string(name);
}

struct RefPath *copy_ref_path(struct RefPath *ref)
{
    if (ref == NULL) {
        return NULL;
    }

    struct RefPath *out = alloc(sizeof(struct RefPath));
    out->tag = ref->tag;
    out->names = copy_name_list(ref->names);
    out->type = ref->type;
    out->parent = copy_ref_path(ref->parent);
    return out;
}

// Note: this handles both match terms and match statements
// (one or other of 'term' or 'stmt' should be NULL).
// For statements, 'mode' is ignored and the addr of the scrutinee should be on the stack.
// For terms, this will itself codegen the scrutinee as needed.
static void codegen_match(struct CGContext *cxt,
                          enum CodegenMode mode,
                          struct Term *term,
                          struct Statement *stmt)
{
    struct StackMachine *mc = cxt->machine;

    struct Term *scrut = term ? term->match.scrutinee : stmt->match.scrutinee;
    struct Arm *arms = term ? term->match.arms : stmt->match.arms;

    struct Type *variant_type = scrut->type;

    // Construct a path for the scrutinee
    // (The match compiler guarantees that the scrutinee will be zero or more
    // TM_FIELD_PROJ's applied to a TM_VAR.)
    struct RefPath *scrut_ref = codegen_ref(cxt, scrut);

    // push a pointer to the scrutinee
    // (only for terms, this is already done for us for statements)
    if (term) {
        codegen_term(cxt, PUSH_ADDR, scrut);
    }

    int num_ifs = 0;

    for (struct Arm *arm = arms; arm; arm = arm->next) {
        // inspect the pattern
        if (arm->pattern->tag == PAT_VARIANT) {
            struct Type *payload_type;
            uint32_t wanted_tag =
                get_tag_number_and_payload_type(variant_type,
                                                arm->pattern->variant.variant_name,
                                                &payload_type);

            // the last arm always matches so no need for "if" in that case
            if (arm->next) {
                // push the scrut tag to the stack
                stk_dup(mc, 0);
                stk_load(mc, false, get_tag_size(variant_type));

                // compare it to the wanted tag
                stk_const(mc, wanted_tag);
                stk_alu(mc, OP_EQ);

                // branch based on the result
                stk_cond_if_nonzero(mc, 1);
                ++num_ifs;
            }

            // Arm matched!

            // We don't need the scrut pointer any more at this point
            stk_pop(mc);

            // Create a new local scope for the pattern-var, and any new
            // vars required by the arm itself
            push_local_scope(cxt);

            if (arm->pattern->variant.payload->tag == PAT_VAR) {
                // make a new reference to the payload
                struct RefPath *path = alloc(sizeof(struct RefPath));
                path->tag = REF_VARIANT_PAYLOAD;
                path->names = NULL;
                path->type = payload_type;
                path->parent = copy_ref_path(scrut_ref);
                add_new_ref(cxt, arm->pattern->variant.payload->var.name, path);
                path = NULL;
            }

            // We can now evaluate the arm!
            if (term) {
                codegen_term(cxt, mode, arm->rhs);
            } else {
                codegen_statements(cxt, arm->rhs);
            }

            // Get rid of the payload variable (and any vars created
            // by the arm itself) afterwards
            pop_local_scope(cxt);

            if (arm->next) {
                stk_cond_else(mc);
            }

        } else if (arm->pattern->tag == PAT_WILDCARD) {

            // We don't need the scrut pointer any more at this point
            stk_pop(mc);

            // Evaluate the arm
            // (This should be done in a new scope)
            push_local_scope(cxt);
            if (term) {
                codegen_term(cxt, mode, arm->rhs);
            } else {
                codegen_statements(cxt, arm->rhs);
            }
            pop_local_scope(cxt);

        } else {
            fatal_error("codegen only supports variant & wildcard patterns");
        }
    }

    free_ref_path(scrut_ref);

    // now close all the ifs :)
    for (int i = 0; i < num_ifs; ++i) {
        stk_cond_endif(mc);
    }
}

static void codegen_sizeof(struct CGContext *cxt,
                           enum CodegenMode mode,
                           struct Term *term)
{
    struct StackMachine *mc = cxt->machine;

    struct Term *rhs = term->sizeof_data.rhs;
    int ndim = array_ndim(rhs->type);

    if (mode == PUSH_VALUE && ndim != 1) {
        fatal_error("codegen_sizeof: PUSH_VALUE can only be used when ndim = 1");
    }
    if (mode == PUSH_ADDR && ndim == 1) {
        fatal_error("codegen_sizeof: PUSH_ADDR can only be used when ndim != 1");
    }

    char name[TEMP_NAME_SIZE];
    if (mode == PUSH_ADDR) {
        get_temp_block_name(cxt, name);
        stk_get_local(mc, name);
    }

    if (rhs->type->tag == TY_DYNAMIC_ARRAY) {
        // Push a pointer to the array.
        codegen_term(cxt, PUSH_ADDR, rhs);

        // The dimensions start at the 8th byte of the array descriptor.
        stk_const(mc, 8);
        stk_alu(mc, OP_ADD);

        if (ndim == 1) {
            // Load the first (and only) dimension.
            stk_load(mc, false, 8);
            if (mode == STORE_TO_MEM) {
                stk_store(mc, 8);
            }

        } else {
            // Memcpy to the correct place.
            memcpy_type(mc, term->type);

            if (mode == PUSH_ADDR) {
                // Get the temp block address back on the stack.
                stk_get_local(mc, name);
            }
        }

    } else if (rhs->type->tag == TY_FIXED_ARRAY) {
        if (ndim == 1) {
            // Push the dimension as a constant
            stk_const(mc, normal_form_to_int(rhs->type->fixed_array_data.sizes[0]));
            if (mode == STORE_TO_MEM) {
                stk_store(mc, 8);
            }

        } else {
            // We must store the dimensions one by one
            // Stack currently contains the place to write to.
            for (int i = 0; i < ndim; ++i) {
                stk_dup(mc, 0);
                if (i != 0) {
                    stk_const(mc, i*8);
                    stk_alu(mc, OP_ADD);
                }
                stk_const(mc, normal_form_to_int(rhs->type->fixed_array_data.sizes[i]));
                stk_store(mc, 8);
            }
            if (mode == STORE_TO_MEM) {
                stk_pop(mc);
            }
        }

    } else {
        fatal_error("Invalid array type tag");
    }
}

static void codegen_array_proj(struct CGContext *cxt,
                               enum CodegenMode mode,
                               struct Term *term)
{
    bool fixed;
    if (term->array_proj.lhs->type->tag == TY_FIXED_ARRAY) {
        fixed = true;
    } else if (term->array_proj.lhs->type->tag == TY_DYNAMIC_ARRAY) {
        fixed = false;
    } else {
        fatal_error("invalid array type for array proj");
    }

    struct StackMachine *mc = cxt->machine;

    // Get the address of the array on top of stack
    codegen_term(cxt, PUSH_ADDR, term->array_proj.lhs);       // [array]

    // Compute the index

    // Note: currently arrays are stored in "row-major order"
    // i.e. array[i,j] is at position (i * dim2 + j)
    // (if the array has size {dim1,dim2}).
    // In other words this is equivalent to array[i][j] in C.

    if (fixed) {
        struct TypeData_FixedArray *data = &term->array_proj.lhs->type->fixed_array_data;

        int n = 1;
        for (struct OpTermList *node = term->array_proj.indexes; node; node = node->next) {
            codegen_term(cxt, PUSH_VALUE, node->rhs);

            uint64_t multiplier = 1;
            for (int i = n; i < data->ndim; ++i) {
                multiplier *= normal_form_to_int(data->sizes[i]);
            }
            if (multiplier != 1) {
                stk_const(mc, multiplier);
                stk_alu(mc, OP_MUL);
            }

            if (n > 1) {
                stk_alu(mc, OP_ADD);
            }

            ++n;
        }

    } else {
        int n = 1;
        for (struct OpTermList *node = term->array_proj.indexes; node; node = node->next) {
            if (n > 1) {
                // [array tot]
                stk_dup(mc, 1);      // [array tot array-ptr]
                stk_const(mc, n*8);  // [array tot array-ptr n*8]
                stk_alu(mc, OP_ADD); // [array tot size-ptr]
                stk_load(mc, false, 8);     // [array tot size]
                stk_alu(mc, OP_MUL); // [array new-tot]
            }

            codegen_term(cxt, PUSH_VALUE, node->rhs);   // [array idx] or [array tot idx]

            if (n > 1) {
                stk_alu(mc, OP_ADD);   // [array tot-idx]
            }

            ++n;
        }
    }

    // Stack now contains: [array tot-idx]
    // Total-index must be multiplied by element-size, then added to the
    // array base pointer.

    struct SizeExpr *size = compute_size_of_type(mc, term->type);
    push_size_expr(mc, size);         // [array tot-idx size]
    free_size_expr(size);
    stk_alu(mc, OP_MUL);              // [array offset]

    if (!fixed) {
        stk_swap(mc, 0, 1);               // [offset array]
        stk_load(mc, false, 8);           // [offset data-ptr]
    }

    stk_alu(mc, OP_ADD);              // [addr]

    switch (mode) {
    case STORE_TO_MEM:
        // [dest-addr src-addr]
        memcpy_type(mc, term->type);
        break;

    case PUSH_VALUE:
        if (is_memory_type(term->type)) {
            fatal_error("can't use PUSH_VALUE with memory type");
        }
        stk_load(mc, is_signed_integral_type(term->type), size_of_integral_type(term->type));
        break;

    case PUSH_ADDR:
        // Nothing else to do
        break;
    }
}


static void codegen_term(struct CGContext *cxt,
                         enum CodegenMode mode,
                         struct Term *term)
{
    switch (term->tag) {
    case TM_VAR: codegen_var(cxt, mode, term->var.name, term->type); break;

    case TM_DEFAULT:
    case TM_MATCH_FAILURE:
        // (For now, a match failure just generates a default value
        // of that type. Perhaps we could have a mode where it
        // crashes the program instead)
        codegen_default(cxt, mode, term->type); break;

    case TM_BOOL_LITERAL: codegen_bool_literal(cxt, mode, term); break;
    case TM_INT_LITERAL: codegen_int_literal(cxt, mode, term); break;
    case TM_STRING_LITERAL: codegen_string_literal(cxt, mode, term); break;
    case TM_CAST: codegen_cast(cxt, mode, term); break;
    case TM_IF: codegen_if(cxt, mode, term); break;
    case TM_UNOP: codegen_unop(cxt, mode, term); break;
    case TM_BINOP: codegen_binop(cxt, mode, term); break;
    case TM_LET: codegen_let(cxt, mode, term); break;
    case TM_QUANTIFIER: fatal_error("unexpected: trying to generate code for quantifier");
    case TM_CALL: codegen_call(cxt, mode, term); break;
    case TM_TYAPP: fatal_error("unexpected: trying to generate code for type-application");
    case TM_RECORD: codegen_record(cxt, mode, term); break;
    case TM_RECORD_UPDATE: codegen_record_update(cxt, mode, term); break;
    case TM_FIELD_PROJ: codegen_field_proj(cxt, mode, term); break;
    case TM_VARIANT: codegen_variant(cxt, mode, term); break;
    case TM_MATCH: codegen_match(cxt, mode, term, NULL); break;
    case TM_SIZEOF: codegen_sizeof(cxt, mode, term); break;
    case TM_ALLOCATED: fatal_error("unexpected: trying to generate code for 'allocated'");
    case TM_ARRAY_PROJ: codegen_array_proj(cxt, mode, term); break;
    }
}


static void push_ref_addr(struct CGContext *context, struct RefPath *path)
{
    struct StackMachine *mc = context->machine;

    bool expect_parent = !(path->tag == REF_VAR || path->tag == REF_STRING_LITERAL);
    bool have_parent = (path->parent != NULL);
    if (expect_parent != have_parent) {
        fatal_error("push_ref_addr: parent mismatches tag");
    }

    if (path->parent) {
        push_ref_addr(context, path->parent);
    }

    switch (path->tag) {
    case REF_VAR:
        codegen_var(context, PUSH_ADDR, path->names->name, path->type);
        break;

    case REF_STRING_LITERAL:
        stk_push_global_addr(mc, path->names->name);
        break;

    case REF_FIELD_PROJ:
        offset_for_field_proj(mc, path->parent->type, path->names->name);
        break;

    case REF_FIXED_ARRAY_PROJ:
        {
            // There is just one name which contains an offset in bytes
            // from the array base.
            stk_get_local(mc, path->names->name);
            stk_alu(mc, OP_ADD);
        }
        break;

    case REF_DYNAMIC_ARRAY_PROJ:
        {
            // This is similar to codegen_array_proj, but slightly different
            // because the indexes are represented by stack-machine vars,
            // rather than Terms.
            int n = 1;

            for (struct NameList *name = path->names; name; name = name->next) {
                if (n > 1) {
                    // [array tot]
                    // We need to multiply tot by size
                    stk_dup(mc, 1);          // [array tot array]
                    stk_const(mc, n*8);      // [array tot array n*8]
                    stk_alu(mc, OP_ADD);     // [array tot size_ptr]
                    stk_load(mc, false, 8);  // [array tot size]
                    stk_alu(mc, OP_MUL);     // [array new_tot]
                }

                stk_get_local(mc, name->name);  // [array idx] or [array tot idx]

                if (n > 1) {
                    stk_alu(mc, OP_ADD);     // [array tot]
                }

                ++n;
            }

            struct SizeExpr *size = compute_size_of_type(mc, path->type);
            push_size_expr(mc, size);
            free_size_expr(size);
            stk_alu(mc, OP_MUL);     // [array offset]
            stk_swap(mc, 0, 1);      // [offset array]
            stk_load(mc, false, 8);  // [offset data-ptr]
            stk_alu(mc, OP_ADD);     // [addr]
        }
        break;

    case REF_VARIANT_PAYLOAD:
        {
            int size = get_tag_size(path->parent->type);
            stk_const(mc, size);
            stk_alu(mc, OP_ADD);
        }
        break;
    }
}


// helper for codegen_ref
static struct NameList * codegen_array_indexes(struct CGContext *cxt, struct OpTermList *terms)
{
    if (terms == NULL) {
        return NULL;
    }

    char *name = next_ref_name(cxt);

    codegen_term(cxt, PUSH_VALUE, terms->rhs);
    stk_create_local(cxt->machine, name, false, 8);
    stk_set_local(cxt->machine, name);

    struct NameList *result = alloc(sizeof(struct NameList));
    result->name = name;
    name = NULL;

    result->next = codegen_array_indexes(cxt, terms->next);

    return result;
}

static struct RefPath * codegen_ref(struct CGContext *cxt, struct Term *term)
{
    struct RefPath *ref = alloc(sizeof(struct RefPath));
    ref->type = term->type;

    switch (term->tag) {
    case TM_VAR:
        ref->tag = REF_VAR;
        ref->names = alloc(sizeof(struct NameList));
        ref->names->name = copy_string(term->var.name);
        ref->names->next = NULL;
        ref->parent = NULL;
        break;

    case TM_STRING_LITERAL:
        add_string_literal(cxt->env, &cxt->strings, term);
        ref->tag = REF_STRING_LITERAL;
        ref->names = alloc(sizeof(struct NameList));
        ref->names->name = copy_string(cxt->strings->name);
        ref->names->next = NULL;
        ref->parent = NULL;
        break;

    case TM_FIELD_PROJ:
        ref->tag = REF_FIELD_PROJ;
        ref->names = alloc(sizeof(struct NameList));
        ref->names->name = copy_string(term->field_proj.field_name);
        ref->names->next = NULL;
        ref->parent = codegen_ref(cxt, term->field_proj.lhs);
        break;

    case TM_ARRAY_PROJ:
        if (term->array_proj.lhs->type->tag == TY_FIXED_ARRAY) {
            struct StackMachine *mc = cxt->machine;

            // Compute the (fixed) array offset in bytes
            struct TypeData_FixedArray *data = &term->array_proj.lhs->type->fixed_array_data;
            int n = 1;
            for (struct OpTermList *node = term->array_proj.indexes; node; node = node->next) {
                codegen_term(cxt, PUSH_VALUE, node->rhs);
                uint64_t multiplier = 1;
                for (int i = n; i < data->ndim; ++i) {
                    multiplier *= normal_form_to_int(data->sizes[i]);
                }
                if (multiplier != 1) {
                    stk_const(mc, multiplier);
                    stk_alu(mc, OP_MUL);
                }
                if (n > 1) {
                    stk_alu(mc, OP_ADD);
                }
                ++n;
            }

            struct SizeExpr *size = compute_size_of_type(mc, term->type);
            push_size_expr(mc, size);
            free_size_expr(size);
            stk_alu(mc, OP_MUL);

            // Store the offset into a variable
            char *name = next_ref_name(cxt);
            stk_create_local(mc, name, false, 8);
            stk_set_local(mc, name);

            // Create the ref, storing that name.
            struct NameList *names = alloc(sizeof(struct NameList));
            names->name = name;
            names->next = NULL;

            ref->tag = REF_FIXED_ARRAY_PROJ;
            ref->names = names;

        } else {
            // For dynamic arrays, we just store the individual array index
            // values, because the array might be re-sized by the time we
            // get to use the reference.
            ref->tag = REF_DYNAMIC_ARRAY_PROJ;
            ref->names = codegen_array_indexes(cxt, term->array_proj.indexes);
        }
        ref->parent = codegen_ref(cxt, term->array_proj.lhs);
        break;

    default:
        fatal_error("codegen_ref: unexpected term tag");
    }

    return ref;
}


// This combines pre_codegen_term and codegen_term in a single function.
// Usable when there is only one term to generate. Call clean_up_temp_blocks
// when you're done with the results.
static void do_codegen_for_term(struct CGContext *cxt,
                                enum CodegenMode mode,
                                const char *store_to_local,
                                struct Term *term)
{
    if (cxt->num_temps != 0) {
        fatal_error("Temporaries have not been cleared from the previous term");
    }
    pre_codegen_term(cxt, store_to_local != NULL, term);

    int saved_num_temps = cxt->num_temps;
    cxt->num_temps = 0;

    if (mode == STORE_TO_MEM) {
        codegen_var(cxt, PUSH_ADDR, store_to_local, term->type);
    }

    codegen_term(cxt, mode, term);

    if (cxt->num_temps != saved_num_temps) {
        fatal_error("do_codegen_for_term: inconsistency detected between pass 1 and 2");
    }
}


static bool normal_form_includes_nonempty_strings(struct Term *term)
{
    switch (term->tag) {
    case TM_DEFAULT:
    case TM_BOOL_LITERAL:
    case TM_INT_LITERAL:
        return false;

    case TM_STRING_LITERAL:
        return term->string_literal.length != 0;

    case TM_RECORD:
        for (struct NameTermList *field = term->record.fields; field; field = field->next) {
            if (normal_form_includes_nonempty_strings(field->term)) {
                return true;
            }
        }
        return false;

    case TM_VARIANT:
        return normal_form_includes_nonempty_strings(term->variant.payload);

    default:
        fatal_error("unrecognised normal form");
    }
}

// This writes the bytes for a normal-form term
// (using stk_insert_byte, etc.)
// It's assume the caller will do the stk_begin_global_constant
// and stk_end_global_constant calls.
// String literals are output to 'strings', the caller should take
// care of these afterwards.
// Size of the term is returned.
static uint64_t codegen_normal_form(struct StackMachine *mc,
                                    struct HashTable *env,
                                    struct StringLiteral **strings,
                                    struct Term *term)
{
    // Compute size of the term
    struct SizeExpr *expr = compute_size_of_type(mc, term->type);
    if (!is_size_expr_const(expr)) fatal_error("size is not known");
    const uint64_t size = get_size_expr_const(expr);
    free_size_expr(expr);

    switch (term->tag) {
    case TM_DEFAULT:
        for (uint64_t n = size; n > 0; --n) {
            stk_insert_byte(mc, 0);
        }
        break;

    case TM_BOOL_LITERAL:
        stk_insert_byte(mc, term->bool_literal.value ? 1 : 0);
        break;

    case TM_INT_LITERAL:
        {
            uint64_t val = normal_form_to_int(term);
            switch (term->type->int_data.num_bits) {
            case 8: stk_insert_byte(mc, val); break;
            case 16: stk_insert_wyde(mc, val); break;
            case 32: stk_insert_tetra(mc, val); break;
            case 64: stk_insert_octa(mc, val); break;
            }
        }
        break;

    case TM_STRING_LITERAL:
        add_string_literal(env, strings, term);
        write_string_descriptor(mc, *strings);
        break;

    case TM_RECORD:
        // just concatenate the fields...
        for (struct NameTermList *field = term->record.fields; field; field = field->next) {
            codegen_normal_form(mc, env, strings, field->term);
        }
        break;

    case TM_VARIANT:
        {
            uint64_t size_written = 0;

            int tag_size = get_tag_size(term->type);
            uint32_t tag_num = get_tag_number_and_payload_type(term->type, term->variant.variant_name, NULL);
            // Write tag
            switch (tag_size) {
            case 1: stk_insert_byte(mc, tag_num); break;
            case 2: stk_insert_wyde(mc, tag_num); break;
            case 4: stk_insert_tetra(mc, tag_num); break;
            }
            size_written += tag_size;

            // Write the payload
            size_written += codegen_normal_form(mc, env, strings, term->variant.payload);

            // Zero pad
            for (uint64_t n = size - size_written; n != 0; --n) {
                stk_insert_byte(mc, 0);
            }
        }
        break;

    default:
        fatal_error("unrecognised normal form");
    }

    return size;
}


//
// Code generation for statements
//

static void codegen_var_decl_stmt(struct CGContext *context, struct Statement *stmt)
{
    struct StackMachine *mc = context->machine;

    if (stmt->var_decl.ref) {
        pre_codegen_term(context, false, stmt->var_decl.rhs);
        context->num_temps = 0;
        struct RefPath * ref = codegen_ref(context, stmt->var_decl.rhs);
        add_new_ref(context, stmt->var_decl.name, ref);
        ref = NULL;

    } else {
        if (is_memory_type(stmt->var_decl.type)) {
            // New local variable: block of memory on the stack
            add_named_mem_block(context, stmt->var_decl.name, stmt->var_decl.type);
            do_codegen_for_term(context, STORE_TO_MEM, stmt->var_decl.name, stmt->var_decl.rhs);

        } else {
            // New local variable, of scalar type
            add_new_local(context, stmt->var_decl.name,
                          is_signed_integral_type(stmt->var_decl.type),
                          size_of_integral_type(stmt->var_decl.type));
            do_codegen_for_term(context, PUSH_VALUE, NULL, stmt->var_decl.rhs);
            stk_set_local(mc, stmt->var_decl.name);
        }
    }

    // Destroy any temporaries that were created by do_codegen_for_term
    // (or pre_codegen_term for refs).
    clean_up_temp_blocks(context);
}

static void codegen_assign_stmt(struct CGContext *context, struct Statement *stmt)
{
    struct StackMachine *mc = context->machine;
    enum TermTag tag = stmt->assign.lhs->tag;

    if (tag == TM_VAR) {
        const char *name;
        struct CodegenItem *item;
        look_up_local_variable(context, stmt->assign.lhs->var.name, &name, &item);

        if (item->ctype == CT_REF || item->ctype == CT_POINTER_ARG || is_memory_type(stmt->assign.lhs->type)) {
            // compute rhs directly into the variable
            do_codegen_for_term(context, STORE_TO_MEM, name, stmt->assign.rhs);

        } else {
            // compute rhs onto stack, then do a set_local
            do_codegen_for_term(context, PUSH_VALUE, NULL, stmt->assign.rhs);
            stk_set_local(mc, name);
        }

    } else {
        // compute the *address* of the LHS onto the stack
        do_codegen_for_term(context, PUSH_ADDR, NULL, stmt->assign.lhs);

        // The addr of the lhs shouldn't point into a temp block,
        // because we're assigning to an lvalue. So it is safe to
        // clean up temp blocks here, and indeed necessary because we
        // are about to call pre_codegen_term, which assumes that
        // context->num_temps has been reset to zero.
        clean_up_temp_blocks(context);

        // compute RHS into the given address
        pre_codegen_term(context, true, stmt->assign.rhs);
        context->num_temps = 0;
        codegen_term(context, STORE_TO_MEM, stmt->assign.rhs);
    }

    clean_up_temp_blocks(context);
}

// Helper for codegen_swap_stmt.
// If lvalue is in memory, push its addr, else push its value.
// Return true if addr was pushed.
// Sets *name if the term is TM_VAR.
// Assumes no temporary blocks exist currently.
static bool codegen_for_swap(struct CGContext *context, struct Term *lvalue, const char **name)
{
    bool need_addr = false;

    if (lvalue->tag != TM_VAR) {
        // A non-var term is a field projection or array projection
        // (or combination thereof), so the value definitely resides
        // in memory
        need_addr = true;

    } else {
        // Even a TM_VAR might reside in memory, if it is CT_REF or CT_POINTER_ARG,
        // or if the variable has a memory type
        struct CodegenItem *item;
        look_up_local_variable(context, lvalue->var.name, name, &item);
        if (item->ctype == CT_REF || item->ctype == CT_POINTER_ARG || is_memory_type(lvalue->type)) {
            need_addr = true;
        }
    }

    // Push either the value or the address as appropriate.
    do_codegen_for_term(context, need_addr ? PUSH_ADDR : PUSH_VALUE, NULL, lvalue);
    clean_up_temp_blocks(context);

    return need_addr;
}

static void codegen_swap_stmt(struct CGContext *context, struct Statement *stmt)
{
    struct StackMachine *mc = context->machine;
    struct Type *type = stmt->swap.lhs->type;

    const char *lhs_name = NULL;
    const char *rhs_name = NULL;

    // put [lhs, rhs] on the stack
    bool lhs_addr = codegen_for_swap(context, stmt->swap.lhs, &lhs_name);
    bool rhs_addr = codegen_for_swap(context, stmt->swap.rhs, &rhs_name);

    if (lhs_addr && rhs_addr) {
        // Memory-to-memory swap.
        push_local_scope(context);
        add_named_mem_block(context, "$swap", type);

        stk_get_local(mc, "$swap");  // [lhs rhs $swap]
        stk_dup(mc, 1);  // [lhs rhs $swap rhs]
        memcpy_type(mc, type);   // $swap = rhs. [lhs rhs]

        stk_dup(mc, 1);  // [lhs rhs lhs]
        memcpy_type(mc, type);  // rhs = lhs.  [lhs]

        stk_get_local(mc, "$swap");   // [lhs $swap]
        memcpy_type(mc, type);  // lhs = $swap. []

        pop_local_scope(context);

    } else if (lhs_addr) {
        // [lhs_addr rhs]
        stk_swap(mc, 0, 1);  // [rhs lhs_addr]
        stk_dup(mc, 0);      // [rhs lhs_addr lhs_addr]
        stk_load(mc, is_signed_integral_type(type), size_of_integral_type(type));  // [rhs lhs_addr lhs]
        stk_set_local(mc, rhs_name);     // rhs = *lhs. [rhs lhs_addr]

        stk_swap(mc, 0, 1);  // [lhs_addr rhs]
        stk_store(mc, size_of_integral_type(type));  // *lhs = old_rhs. []

    } else if (rhs_addr) {
        // [lhs rhs_addr]
        stk_dup(mc, 0);   // [lhs rhs_addr rhs_addr]
        stk_load(mc, is_signed_integral_type(type), size_of_integral_type(type));  // [lhs rhs_addr rhs]
        stk_set_local(mc, lhs_name);     // lhs = *rhs. [lhs rhs_addr]

        stk_swap(mc, 0, 1);  // [rhs_addr lhs]
        stk_store(mc, size_of_integral_type(type));  // *rhs = old_lhs. []

    } else {
        // We have two "register" values, we can just assign back to the variables.
        // Note both terms are TM_VAR in this case.
        stk_set_local(mc, lhs_name);
        stk_set_local(mc, rhs_name);
    }
}

static void codegen_return_stmt(struct CGContext *context, struct Statement *stmt)
{
    struct StackMachine *mc = context->machine;

    if (stmt->ret.value) {
        if (is_memory_type(stmt->ret.value->type)) {
            // save value to the "return" memory block
            do_codegen_for_term(context, STORE_TO_MEM, "return", stmt->ret.value);
        } else {
            // leave value on the stack
            do_codegen_for_term(context, PUSH_VALUE, NULL, stmt->ret.value);
        }
    }

    stk_return_from_function(mc);

    clean_up_temp_blocks(context);
}

static void codegen_if_stmt(struct CGContext *context, struct Statement *stmt)
{
    struct StackMachine *mc = context->machine;

    do_codegen_for_term(context, PUSH_VALUE, NULL, stmt->if_data.condition);
    clean_up_temp_blocks(context);

    stk_cond_if_nonzero(mc, 1);

    push_local_scope(context);
    codegen_statements(context, stmt->if_data.then_block);
    pop_local_scope(context);

    stk_cond_else(mc);

    push_local_scope(context);
    codegen_statements(context, stmt->if_data.else_block);
    pop_local_scope(context);

    stk_cond_endif(mc);
}

static void codegen_while_stmt(struct CGContext *context, struct Statement *stmt)
{
    struct StackMachine *mc = context->machine;

    stk_loop_begin(mc);

    // If NOT condition, then go to end of loop
    do_codegen_for_term(context, PUSH_VALUE, NULL, stmt->while_data.condition);
    stk_cond_if_zero(mc, 1);

    clean_up_temp_blocks(context);

    stk_loop_goto_end(mc);
    stk_cond_endif(mc);

    // Do loop body (in new scope)
    push_local_scope(context);
    codegen_statements(context, stmt->while_data.body);
    pop_local_scope(context);

    // Jump back to top of loop
    stk_loop_goto_beginning(mc);

    stk_loop_end(mc);
}

static void codegen_statements(struct CGContext *context, struct Statement *stmts)
{
    while (stmts && stk_is_reachable(context->machine)) {
        if (!stmts->ghost) {
            switch (stmts->tag) {
            case ST_FIX:
            case ST_USE:
            case ST_OBTAIN:
            case ST_ASSUME:
            case ST_ASSERT:
            case ST_SHOW_HIDE:
                // these should always be ghost
                fatal_error("codegen_statements: non-ghost fix/use/etc.");

            case ST_VAR_DECL:
                codegen_var_decl_stmt(context, stmts);
                break;

            case ST_ASSIGN:
                codegen_assign_stmt(context, stmts);
                break;

            case ST_SWAP:
                codegen_swap_stmt(context, stmts);
                break;

            case ST_RETURN:
                codegen_return_stmt(context, stmts);
                break;

            case ST_IF:
                codegen_if_stmt(context, stmts);
                break;

            case ST_WHILE:
                codegen_while_stmt(context, stmts);
                break;

            case ST_CALL:
                do_codegen_for_term(context, PUSH_VALUE, NULL, stmts->call.term);
                clean_up_temp_blocks(context);
                break;

            case ST_MATCH:
                do_codegen_for_term(context, PUSH_ADDR, NULL, stmts->match.scrutinee);
                codegen_match(context, 0, NULL, stmts);
                clean_up_temp_blocks(context);
                break;

            case ST_MATCH_FAILURE:
                // Just do nothing
                break;
            }
        }

        stmts = stmts->next;
    }
}



//
// Code generation for decls
//

static void codegen_decl_const(struct HashTable *env,
                               struct StackMachine *mc,
                               struct Decl *decl)
{
    if (!decl->const_data.rhs) return;
    if (!decl->const_data.value) fatal_error("constant value is not known");

    struct StringLiteral *strings = NULL;

    // Generate the constant
    char *name = mangle_name(decl->name);
    stk_begin_global_constant(mc, name, normal_form_includes_nonempty_strings(decl->const_data.value), true);
    free(name);
    name = NULL;
    codegen_normal_form(mc, env, &strings, decl->const_data.value);
    stk_end_global_constant(mc);

    // Generate any string data required
    create_string_literals(mc, strings, false);

    // Put the constant in the env
    struct CodegenItem *new_item = alloc(sizeof(struct CodegenItem));
    new_item->ctype = CT_GLOBAL_VAR;
    hash_table_insert(env, copy_string(decl->name), new_item);
}

static void codegen_decl_function(struct HashTable *env,
                                  struct StackMachine *mc,
                                  struct Decl *decl)
{
    if (decl->function_data.is_extern) {
        // Extern function. Just insert a CodegenItem and we're done.
        struct CodegenItem *item = alloc(sizeof(struct CodegenItem));
        item->ctype = CT_FUNCTION;

        const char *dot = strrchr(decl->name, '.');
        if (dot == NULL) {
            fatal_error("unexpected: decl without '.' in name");
        }
        item->foreign_name = copy_string(dot + 1);

        hash_table_insert(env, copy_string(decl->name), item);
        return;
    }

    if (!decl->function_data.body_specified) {
        // This must be an interface decl
        return;
    }

    // Start a new function
    char *fun_name = mangle_name(decl->name);
    struct CGContext *context = new_cg_context(env, mc, fun_name);
    free(fun_name);

    // Add a new scope to hold the outermost locals, and arguments.
    push_local_scope(context);

    // If the return type is a struct then add an extra implicit pointer argument
    if (decl->function_data.return_type
    && is_memory_type(decl->function_data.return_type)) {
        add_new_local(context, "return", false, 8);
    }

    // Add the type variables - and their hidden size arguments
    context->tyvars = copy_tyvar_list(decl->function_data.tyvars);
    for (struct TyVarList *tv = context->tyvars; tv; tv = tv->next) {
        add_new_local(context, tv->name, false, 8);
    }

    // Add the arguments
    for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
        if (arg->ref) {
            // ref args are always passed by pointer
            add_to_scope(context, arg->name, CT_POINTER_ARG, NULL);
            stk_create_local(context->machine, arg->name, false, 8);

        } else {
            // non-ref args are passed by pointer if they are a
            // "memory type" or by value if they are a "non-memory
            // type" (int or bool)
            int size = type_or_pointer_size(arg->type);
            bool is_signed = is_signed_integral_type(arg->type);
            add_new_local(context, arg->name, is_signed, size);
        }
    }

    stk_finish_arguments(context->machine);

    // Generate code for the statements of the function
    codegen_statements(context, decl->function_data.body);

    // The scope is no longer needed
    pop_local_scope(context);

    // Finalise the generated code
    free_cg_context(context);

    // Create an item in the env
    struct CodegenItem *item = alloc(sizeof(struct CodegenItem));
    item->ctype = CT_FUNCTION;
    item->foreign_name = NULL;
    hash_table_insert(env, copy_string(decl->name), item);
}

// codegens a single Decl
static void codegen_decl(struct HashTable *env,
                         struct StackMachine *mc,
                         struct Decl *decl)
{
    if (decl->ghost) {
        return;
    }

    switch (decl->tag) {
    case DECL_CONST:
        codegen_decl_const(env, mc, decl);
        break;

    case DECL_FUNCTION:
        codegen_decl_function(env, mc, decl);
        break;

    case DECL_DATATYPE:
    case DECL_TYPEDEF:
        // Nothing to do
        break;
    }
}

static void codegen_root(struct HashTable *env,
                         struct StackMachine *mc,
                         struct Module *module,
                         bool generate_main)
{
    // RTS functions
    stk_make_rts_functions(mc);

    // C main function
    if (generate_main) {
        stk_begin_function(mc, "main");
        stk_prepare_function_call(mc, 0);
        char *main_name = copy_string_2(module->name, "_main");
        stk_emit_function_call(mc, main_name, false);
        free(main_name);
        stk_const(mc, 0);
        stk_return_from_function(mc);
        stk_end_function(mc);
    }
}

struct HashTable * new_codegen_env()
{
    return new_hash_table();
}

static void free_codegen_item(void *context, const char *key, void *value)
{
    struct CodegenItem *item = value;
    if (item->ctype == CT_FUNCTION) {
        free((char*)item->foreign_name);
    } else if (item->ctype == CT_REF) {
        free_ref_path(item->path);
    }
    free((void*)key);
    free(item);
}

void free_codegen_env(struct HashTable *env)
{
    hash_table_remove(env, "$StringNum");
    hash_table_for_each(env, free_codegen_item, NULL);
    free_hash_table(env);
}

void codegen_module(FILE *asm_output_file, struct HashTable *env, struct Module *module, bool root, bool generate_main)
{
    struct StackMachine *mc = stk_create(asm_output_file);

    for (struct DeclGroup *decls = module->interface; decls; decls = decls->next) {
        for (struct Decl *decl = decls->decl; decl; decl = decl->next) {
            codegen_decl(env, mc, decl);
        }
    }

    for (struct DeclGroup *decls = module->implementation; decls; decls = decls->next) {
        for (struct Decl *decl = decls->decl; decl; decl = decl->next) {
            codegen_decl(env, mc, decl);
        }
    }

    if (root) {
        codegen_root(env, mc, module, generate_main);
    }

    stk_destroy(mc);
}
