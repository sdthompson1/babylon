/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


/*

This converts a Babylon module into a C translation unit (.c and .h file pair).

We make the following assumptions about the target C compiler:

 - The compiler conforms to the C standard (C99 or later).

 - The compiler supports variable length arrays (VLAs).

 - The target machine represents integers using a conventional twos-complement
   representation, with no padding bits, no trap representations, etc.

 - The exact-width integer types (uint8_t, int16_t etc.) are available,
   in sizes of (at least) 8, 16, 32 and 64 bits.

 - Right shifts of negative numbers perform an arithmetic right shift.
   (The C standard leaves this implementation-defined, but in practice
   most compilers will do an arithmetic shift in this case.)

Note that we do NOT assume anything about sizeof(int), sizeof(void*), pointer
representations, endianness, 32-bit vs 64-bit, or anything of that sort.

*/


#include "alloc.h"
#include "ast.h"
#include "codegen.h"
#include "cprint.h"
#include "error.h"
#include "hash_table.h"
#include "normal_form.h"
#include "size_expr.h"
#include "util.h"

#include <ctype.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


//
// Codegen data structures
//

struct CodegenEntry {
    bool is_ref;                // true if 'ref' variable.
    bool is_func_const;         // true if 'const' decl represented by a function.
    const char *foreign_name;   // non-NULL if 'extern' func. points to allocated mem.
    bool is_abstract_type;      // true if abstract type decl ("type Foo;").
};

struct CGContext {
    struct HashTable *env;
    struct CPrinter *pr;
    struct CPrinter *h_pr;
    uint64_t tmp_num;
};

static void reset_context(struct CGContext *cxt)
{
    cxt->tmp_num = 0;
}

static bool is_ref_var(struct CGContext *cxt, const char *name)
{
    struct CodegenEntry *entry = hash_table_lookup(cxt->env, name);
    return entry && entry->is_ref;
}

static bool is_func_const(struct CGContext *cxt, const char *name)
{
    struct CodegenEntry *entry = hash_table_lookup(cxt->env, name);
    return entry && entry->is_func_const;
}

static bool is_abstract_type(struct CGContext *cxt, const char *name)
{
    struct CodegenEntry *entry = hash_table_lookup(cxt->env, name);
    return entry && entry->is_abstract_type;
}


//
// Z-encoding of names
//

// Identifiers are encoded into C as follows:

// "."         => "z_"
// "@"         => "za"
// "^"         => "zh"
// Leading "_" => "zu"
// "z"         => "zz"

// Any other underscore, any digit 0-9, or any letter a-z or A-Z maps
// to itself.

// If the entire result comes out equal to a C keyword, or an
// otherwise reserved name, then a lone "z" is appended.

static bool valid_char(char ch)
{
    return isalnum(ch) || ch == '_';
}

static uint64_t encode_chars(const char *input, char *output)
{
    uint64_t num = 0;
    while (*input) {
        switch (*input) {
        case '.':
            num += 2;
            if (output) { *output++ = 'z'; *output++ = '_'; }
            break;

        case '@':
            num += 2;
            if (output) { *output++ = 'z'; *output++ = 'a'; }
            break;

        case '^':
            num += 2;
            if (output) { *output++ = 'z'; *output++ = 'h'; }
            break;

        case 'z':
            num += 2;
            if (output) { *output++ = 'z'; *output++ = 'z'; }
            break;

        case '_':
            if (num == 0) {
                num += 2;
                if (output) { *output++ = 'z'; *output++ = 'u'; }
                break;
            }
            // Fall through

        default:
            if (!valid_char(*input)) {
                fatal_error("encoding identifier to C failed");
            }

            num += 1;
            if (output) *output++ = *input;
        }

        input++;
    }

    num++;
    if (output) *output = 0;

    return num;
}

static const char * RESERVED_NAMES[] = {
    // Keywords - based on the C11 standard.
    // (We omit the keywords that begin with "_", because initial
    // underscores are z-encoded away.)
    "alignof",
    "auto",
    "break",
    "case",
    "char",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extern",
    "float",
    "for",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "register",
    "restrict",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "struct",
    "switch",
    "typedef",
    "union",
    "unsigned",
    "void",
    "volatile",
    "while",

    // "ret" is reserved as an argument name (for functions that return aggregates).
    "ret",

    // "memcpy", "memmove" and "memset" are called by the compiled code, so naming
    // local variables after them would cause problems.
    "memcpy",
    "memmove",
    "memset",

    // TODO: It might be necessary to add other reserved names to this list.
    // A close reading of the section(s) on reserved identifiers in the C standard
    // might be a good idea!

    NULL
};

static bool is_reserved(const char *name)
{
    // check the list of known reserved names
    const char **kw = RESERVED_NAMES;
    while (*kw) {
        if (strcmp(*kw, name) == 0) {
            return true;
        }
        kw++;
    }

    // also any name of the form "tmp" + numeric digits is reserved
    if (name[0] == 't' && name[1] == 'm' && name[2] == 'p') {
        const char *p = &name[3];
        bool all_digits = true;
        while (*p) {
            if (!isdigit(*p)) {
                all_digits = false;
                break;
            }
            p++;
        }
        if (all_digits) return true;
    }

    // anything else is OK
    return false;
}

static char * mangle_name(const char *input)
{
    uint64_t len = encode_chars(input, NULL);

    char *buf = alloc(len + 1);
    encode_chars(input, buf);

    if (is_reserved(buf)) {
        buf[len - 1] = 'z';
        buf[len] = 0;
    }

    return buf;
}


//
// TermMode and Priority enums
//

// TermMode only affects scalar types. The term is generated as an integer expression
// in MODE_VALUE, or a char* pointer in MODE_ADDR.

// Aggregates always map to char* regardless of TermMode.

enum TermMode {
    MODE_VALUE,
    MODE_ADDR
};

enum Priority {
    // lowest priority
    EXPR,
    ASSIGN_EXPR,
    COND_EXPR,
    LOG_OR_EXPR,
    LOG_AND_EXPR,
    BIT_OR_EXPR,
    BIT_XOR_EXPR,
    BIT_AND_EXPR,
    EQ_EXPR,
    REL_EXPR,
    SHIFT_EXPR,
    ADD_EXPR,
    MULT_EXPR,
    CAST_EXPR,
    UNARY_EXPR,
    POSTFIX_EXPR,
    PRIMARY_EXPR
    // highest priority
};


//
// Code generation for types
//

static bool is_scalar_type(struct CGContext *cxt, const struct Type *type)
{
    if (type->tag == TY_BOOL || type->tag == TY_FINITE_INT) {
        return true;
    } else if (type->tag == TY_VAR) {
        // Abstract typedefs are actually scalars (of type void*).
        // Anything else is a generic type parameter, which is considered
        // an aggregate type.
        return is_abstract_type(cxt, type->var_data.name);
    } else {
        return false;
    }
}

static const char * scalar_type_to_name(struct Type *type)
{
    switch (type->tag) {
    case TY_BOOL:
        // We could also use _Bool here, but sizeof(_Bool) isn't defined by the
        // standard (i.e. it might be more than 1 on some compilers) whereas
        // uint8_t has a well-defined size (1 byte) and representation.
        return "uint8_t";

    case TY_FINITE_INT:
        if (type->int_data.is_signed) {
            switch (type->int_data.num_bits) {
            case 8: return "int8_t";
            case 16: return "int16_t";
            case 32: return "int32_t";
            case 64: return "int64_t";
            default: fatal_error("wrong number of bits");
            }
        } else {
            switch (type->int_data.num_bits) {
            case 8: return "uint8_t";
            case 16: return "uint16_t";
            case 32: return "uint32_t";
            case 64: return "uint64_t";
            default: fatal_error("wrong number of bits");
            }
        }

    case TY_VAR:
        return "void*";

    default:
        fatal_error("not a scalar type");
    }
}

// this outputs int8_t (etc.) (or void*) for scalar types,
// or char* for aggregate types.
static void codegen_type(struct CGContext *cxt,
                         struct Type *type)
{
    switch (type->tag) {
    case TY_VAR:
        if (is_abstract_type(cxt, type->var_data.name)) {
            print_token(cxt->pr, "void");
        } else {
            print_token(cxt->pr, "char");
        }
        print_token(cxt->pr, "*");
        break;

    case TY_BOOL:
    case TY_FINITE_INT:
        print_token(cxt->pr, scalar_type_to_name(type));
        break;

    case TY_RECORD:
    case TY_VARIANT:
    case TY_FIXED_ARRAY:
    case TY_DYNAMIC_ARRAY:
        print_token(cxt->pr, "char");
        print_token(cxt->pr, "*");
        break;

    case TY_MATH_INT:
    case TY_MATH_REAL:
    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
    case TY_APP:
        fatal_error("cannot codegen this type");
    }
}


//
// Temporary names
//

#define TEMP_NAME_LEN 50

// Get the name of the next available temporary variable.
static void get_temp_name(struct CGContext *cxt,
                          char name[TEMP_NAME_LEN])
{
    sprintf(name, "tmp%" PRIu64, cxt->tmp_num++);
}


//
// Size computations
//

static char* temp_name_func(void *cxt)
{
    char name[TEMP_NAME_LEN];
    get_temp_name(cxt, name);
    return copy_string(name);
}

static void print_size_expr(struct CGContext *cxt,
                            enum Priority pri,
                            struct SizeExpr *expr)
{
    if (pri > ADD_EXPR) print_token(cxt->pr, "(");
    write_size_expr(cxt->pr, expr, temp_name_func, cxt);
    if (pri > ADD_EXPR) print_token(cxt->pr, ")");
}

static int get_tag_size(struct Type *variant_type, const char **c_type_name)
{
    if (variant_type->tag != TY_VARIANT) fatal_error("get_tag_size called with wrong type");

    uint32_t num_tags = 0;
    for (struct NameTypeList *variant = variant_type->variant_data.variants; variant; variant = variant->next) {
        ++num_tags;
        if (num_tags == 0) fatal_error("too many variants");
    }
    if (num_tags <= 256) {
        if (c_type_name) *c_type_name = "uint8_t";
        return 1;
    } else if (num_tags <= 65536) {
        if (c_type_name) *c_type_name = "uint16_t";
        return 2;
    } else {
        if (c_type_name) *c_type_name = "uint32_t";
        return 4;
    }
}

static uint32_t get_tag_number_and_payload_type(struct Type *variant_type,
                                                const char *name,
                                                struct Type **payload_type_out)
{
    if (variant_type->tag != TY_VARIANT) fatal_error("get_tag_number_and_payload_type: wrong type");
    uint32_t num = 0;
    for (struct NameTypeList *variant = variant_type->variant_data.variants; variant; variant = variant->next) {
        if (strcmp(name, variant->name) == 0) {
            if (payload_type_out) *payload_type_out = variant->type;
            return num;
        }
        ++num;
        if (num == 0) fatal_error("too many variants");
    }
    fatal_error("variant tag not found");
}

static struct SizeExpr * get_size_of_type(struct CGContext *cxt,
                                          struct Type *type)
{
    switch (type->tag) {
    case TY_VAR:
        if (is_abstract_type(cxt, type->var_data.name)) {
            // Abstract types are always represented as void*
            return var_size_expr("sizeof(void*)", 1);
        } else {
            // It must be a generic type parameter, so the size is represented
            // by a variable.
            char *mangled_name = mangle_name(type->var_data.name);
            struct SizeExpr *result = var_size_expr(mangled_name, 1);
            free(mangled_name);
            return result;
        }

    case TY_BOOL:
        // TY_BOOL converts to uint8_t which has size 1.
        return const_size_expr(1);

    case TY_FINITE_INT:
        // We assume that the intN_t and uintN_t types have the
        // standard sizes (1, 2, 4 or 8).
        // I think this is legitimate (according to the C standard)
        // because, if uint8_t and int8_t exist at all, they must have
        // exactly 8 bits (with no padding) which means that CHAR_BIT
        // must be 8. Therefore the other intN_t types must have the
        // expected sizes as well.
        return const_size_expr(type->int_data.num_bits / 8);

    case TY_RECORD:
        {
            struct SizeExpr *size = zero_size_expr();
            for (struct NameTypeList *field = type->record_data.fields; field; field = field->next) {
                struct SizeExpr *field_size = get_size_of_type(cxt, field->type);
                struct SizeExpr *sum = add_size_expr(field_size, size);
                free_size_expr(size);
                free_size_expr(field_size);
                size = sum;
            }
            return size;
        }

    case TY_VARIANT:
        {
            struct SizeExpr *size = zero_size_expr();
            for (struct NameTypeList *variant = type->variant_data.variants; variant; variant = variant->next) {
                struct SizeExpr *variant_size = get_size_of_type(cxt, variant->type);
                struct SizeExpr *new_size = max_size_expr(size, variant_size);
                free_size_expr(size);
                free_size_expr(variant_size);
                size = new_size;
            }
            struct SizeExpr *tag_size = const_size_expr(get_tag_size(type, NULL));
            struct SizeExpr *result = add_size_expr(size, tag_size);
            free_size_expr(size);
            free_size_expr(tag_size);
            return result;
        }

    case TY_FIXED_ARRAY:
        {
            struct SizeExpr *size = get_size_of_type(cxt, type->fixed_array_data.element_type);
            for (int i = 0; i < type->fixed_array_data.ndim; ++i) {
                uint64_t dim = normal_form_to_int(type->fixed_array_data.sizes[i]);
                struct SizeExpr *new_size = multiply_size_expr(dim, size);
                free_size_expr(size);
                size = new_size;
            }

            return size;
        }

    case TY_DYNAMIC_ARRAY:
        {
            // dynamic array descriptor = pointer to data + dimensions as u64's
            // note this is independent of the element size
            struct SizeExpr *size1 = var_size_expr("sizeof(void*)", 1);
            struct SizeExpr *size2 = const_size_expr(8 * type->dynamic_array_data.ndim);
            struct SizeExpr *result = add_size_expr(size1, size2);
            free_size_expr(size1);
            free_size_expr(size2);
            return result;
        }

    case TY_MATH_INT:
    case TY_MATH_REAL:
    case TY_FUNCTION:
    case TY_FORALL:
    case TY_LAMBDA:
    case TY_APP:
        fatal_error("get_size_of_type: improper argument");
    }

    fatal_error("get_size_of_type: unrecognised type->tag");
}

static struct SizeExpr * get_field_offset(struct CGContext *cxt,
                                          struct Type *record_type,
                                          const char *field_name)
{
    if (record_type->tag != TY_RECORD) fatal_error("get_field_offset: requires a record type");

    struct SizeExpr *size = zero_size_expr();
    for (struct NameTypeList *field = record_type->record_data.fields; field; field = field->next) {
        if (strcmp(field->name, field_name) == 0) {
            return size;
        }
        struct SizeExpr *field_size = get_size_of_type(cxt, field->type);
        struct SizeExpr *sum = add_size_expr(field_size, size);
        free_size_expr(size);
        free_size_expr(field_size);
        size = sum;
    }
    fatal_error("get_field_offset: field not found");
}

static void print_size_of_type(struct CGContext *cxt,
                               enum Priority pri,
                               struct Type *type)
{
    struct SizeExpr *size = get_size_of_type(cxt, type);
    print_size_expr(cxt, pri, size);
    free_size_expr(size);
}


//
// Variable declarations (including temporaries)
//

// Declare a variable, as either an appropriate integer type (for scalars)
// or a char array (for aggregates).
static void declare_variable(struct CGContext *cxt,
                             char *mangled_name,
                             struct Type *type,
                             bool is_static);

// Combination of get_temp_name and declare_variable.
static void make_temporary(struct CGContext *cxt,
                           char name[TEMP_NAME_LEN],
                           struct Type *type)
{
    get_temp_name(cxt, name);
    declare_variable(cxt, name, type, false);
}

static void make_static_temporary(struct CGContext *cxt,
                                  char name[TEMP_NAME_LEN],
                                  struct Type *type)
{
    get_temp_name(cxt, name);
    declare_variable(cxt, name, type, true);
}

static void declare_scalar(struct CGContext *cxt,
                           char *mangled_name,
                           const char *type_name)
{
    print_token(cxt->pr, type_name);
    print_token(cxt->pr, mangled_name);
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
}

static void declare_aggregate(struct CGContext *cxt,
                              char *mangled_name,
                              struct Type *type)
{
    print_token(cxt->pr, "char");
    print_token(cxt->pr, mangled_name);
    print_token(cxt->pr, "[");

    // technically speaking array sizes are not allowed to be zero, hence,
    // we use the max of 1 and the actual size of the type
    struct SizeExpr *size = get_size_of_type(cxt, type);
    struct SizeExpr *one = const_size_expr(1);
    struct SizeExpr *modified_size = max_size_expr(size, one);
    free_size_expr(size);
    free_size_expr(one);
    print_size_expr(cxt, ASSIGN_EXPR, modified_size);
    free_size_expr(modified_size);

    print_token(cxt->pr, "]");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
}

static void declare_variable(struct CGContext *cxt,
                             char *mangled_name,
                             struct Type *type,
                             bool is_static)
{
    begin_item(cxt->pr);

    if (is_static) {
        print_token(cxt->pr, "static");
    }

    if (is_scalar_type(cxt, type)) {
        declare_scalar(cxt, mangled_name, scalar_type_to_name(type));
    } else {
        declare_aggregate(cxt, mangled_name, type);
    }

    end_item(cxt->pr);
}


//
// Code generation for terms
//

static void codegen_term(struct CGContext *cxt,
                         enum Priority pri,
                         enum TermMode mode,
                         struct Term *term);

static void codegen_statements(struct CGContext *cxt,
                               struct Statement *stmts);

static bool is_lvalue(struct Term *term)
{
    return term->tag == TM_VAR
        || term->tag == TM_STRING_LITERAL
        || term->tag == TM_FIELD_PROJ
        || term->tag == TM_ARRAY_PROJ;
}

static void memmove_begin(struct CGContext *cxt)
{
    print_token(cxt->pr, "memmove");
    print_token(cxt->pr, "(");
}

static void memmove_end(struct CGContext *cxt, struct Type *type)
{
    print_token(cxt->pr, ",");
    print_size_of_type(cxt, ASSIGN_EXPR, type);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
}

// Copy contents of rhs into the variable "mangled_name", or, if
// is_ref is true, to the memory pointed to by "mangled_name" (a char*
// pointer). (is_ref only makes any difference for scalar types.)
static void copy_term_to_variable(struct CGContext *cxt,
                                  const char *mangled_name,
                                  bool is_ref,
                                  struct Term *rhs)
{
    begin_item(cxt->pr);
    if (!is_scalar_type(cxt, rhs->type) || is_ref) {
        memmove_begin(cxt);
        print_token(cxt->pr, mangled_name);
        print_token(cxt->pr, ",");
        codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, rhs);
        memmove_end(cxt, rhs->type);
    } else {
        print_token(cxt->pr, mangled_name);
        print_token(cxt->pr, "=");
        codegen_term(cxt, ASSIGN_EXPR, MODE_VALUE, rhs);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
    }
    end_item(cxt->pr);
}

// Copy a variable to a term. The variable is assumed NOT to be a reference.
// (This is used in codegen for swap statements.)
static void copy_variable_to_term(struct CGContext *cxt,
                                  struct Term *lhs,
                                  const char *rhs_mangled_name)
{
    bool scalar = is_scalar_type(cxt, lhs->type);

    begin_item(cxt->pr);
    if (scalar && lhs->tag == TM_VAR && !is_ref_var(cxt, lhs->var.name)) {
        char *lhs_mangled_name = mangle_name(lhs->var.name);
        print_token(cxt->pr, lhs_mangled_name);
        free(lhs_mangled_name);
        print_token(cxt->pr, "=");
        print_token(cxt->pr, rhs_mangled_name);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
    } else {
        memmove_begin(cxt);
        codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, lhs);
        print_token(cxt->pr, ",");
        if (scalar) print_token(cxt->pr, "&");
        print_token(cxt->pr, rhs_mangled_name);
        memmove_end(cxt, lhs->type);
    }
    end_item(cxt->pr);
}

// Copy rhs to lhs. The two terms must have the same type.
static void copy_term_to_term(struct CGContext *cxt,
                              struct Term *lhs,
                              struct Term *rhs)
{
    begin_item(cxt->pr);
    if (lhs->tag == TM_VAR && is_scalar_type(cxt, lhs->type) && !is_ref_var(cxt, lhs->var.name)) {
        char *mangled_name = mangle_name(lhs->var.name);
        print_token(cxt->pr, mangled_name);
        free(mangled_name);
        print_token(cxt->pr, "=");
        codegen_term(cxt, ASSIGN_EXPR, MODE_VALUE, rhs);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
    } else {
        memmove_begin(cxt);
        codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, lhs);
        print_token(cxt->pr, ",");
        codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, rhs);
        memmove_end(cxt, rhs->type);
    }
    end_item(cxt->pr);
}

static void codegen_var(struct CGContext *cxt,
                        enum Priority pri,
                        enum TermMode mode,
                        struct Term *term)
{
    bool ref = is_ref_var(cxt, term->var.name);
    bool scalar = is_scalar_type(cxt, term->type);
    char *mangled_name = mangle_name(term->var.name);

    if (scalar && mode == MODE_VALUE) {
        if (ref) {
            // need to read value of reference using memmove
            char temp_name[TEMP_NAME_LEN];
            make_temporary(cxt, temp_name, term->type);

            begin_item(cxt->pr);
            memmove_begin(cxt);
            print_token(cxt->pr, "&");
            print_token(cxt->pr, temp_name);
            print_token(cxt->pr, ",");
            print_token(cxt->pr, mangled_name);
            memmove_end(cxt, term->type);
            end_item(cxt->pr);

            print_token(cxt->pr, temp_name);

        } else {
            // return value of scalar directly
            print_token(cxt->pr, mangled_name);
        }
    } else if (scalar && mode == MODE_ADDR) {
        if (ref) {
            // return reference (of type char*) directly
            print_token(cxt->pr, mangled_name);
        } else {
            // return address of the variable using "&" operator,
            // but cast to char*
            if (pri > CAST_EXPR) print_token(cxt->pr, "(");
            print_token(cxt->pr, "(");
            print_token(cxt->pr, "char");
            print_token(cxt->pr, "*");
            print_token(cxt->pr, ")");
            print_token(cxt->pr, "&");
            print_token(cxt->pr, mangled_name);
            if (pri > CAST_EXPR) print_token(cxt->pr, ")");
        }
    } else if (is_func_const(cxt, term->var.name)) {
        // function call required to get the value
        if (pri > POSTFIX_EXPR) print_token(cxt->pr, "(");
        print_token(cxt->pr, mangled_name);
        print_token(cxt->pr, "(");
        print_token(cxt->pr, ")");
        if (pri > POSTFIX_EXPR) print_token(cxt->pr, ")");
    } else {
        // aggregate, always represented as char* (whether ref or not) so
        // we can just return the variable. (mode is irrelevant in this case.)
        print_token(cxt->pr, mangled_name);
    }

    free(mangled_name);
}

static void codegen_default(struct CGContext *cxt,
                            enum Priority pri,
                            enum TermMode mode,
                            struct Term *term)
{
    if (is_scalar_type(cxt, term->type)) {
        // note: MODE_ADDR is handled elsewhere (in codegen_term itself)
        if (mode == MODE_ADDR) fatal_error("unexpected: MODE_ADDR in codegen_default");
        print_token(cxt->pr, "0");

    } else {
        char name[TEMP_NAME_LEN];
        make_temporary(cxt, name, term->type);

        // Zero-initialise using memset.
        // (The alternative would be to initialise with "={0};", but this doesn't
        // work with variable-length arrays.)
        begin_item(cxt->pr);
        print_token(cxt->pr, "memset");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, name);
        print_token(cxt->pr, ",");
        print_token(cxt->pr, "0");
        print_token(cxt->pr, ",");
        print_size_of_type(cxt, ASSIGN_EXPR, term->type);
        print_token(cxt->pr, ")");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        print_token(cxt->pr, name);
    }
}

static void codegen_bool_literal(struct CGContext *cxt,
                                 enum Priority pri,
                                 enum TermMode mode,
                                 struct Term *term)
{
    if (mode == MODE_ADDR) fatal_error("unexpected: MODE_ADDR in codegen_bool_literal");
    print_token(cxt->pr, term->bool_literal.value ? "1" : "0");
}

static uint64_t largest_negative(int num_bits)
{
    switch (num_bits) {
    case 8:  return UINT64_C(0xffffffffffffff80);
    case 16: return UINT64_C(0xffffffffffff8000);
    case 32: return UINT64_C(0xffffffff80000000);
    case 64: return UINT64_C(0x8000000000000000);
    default: fatal_error("wrong number of bits");
    }
}

static void codegen_int_literal(struct CGContext *cxt,
                                enum Priority pri,
                                enum TermMode mode,
                                struct Term *term)
{
    if (mode != MODE_VALUE) fatal_error("unexpected: MODE_ADDR in codegen_int_literal");

    char buf[50];

    uint64_t num = parse_int_literal(term->int_literal.data);

    // Use the INTn_C or UINTn_C macros to ensure we get the correct types for
    // our integer literals.

    // For negative numbers, apparently we can't write INT32_C(-1), we have to
    // write -INT32_C(1) instead. Also we must be careful about the largest negative
    // number because its positive form will be an overflow for the type.

    if (term->type->int_data.is_signed
    && num == largest_negative(term->type->int_data.num_bits)) {
        num = ~num;
        sprintf(buf,
                "~INT%d_C(0x%" PRIx64 ")",
                term->type->int_data.num_bits,
                num);
        if (pri > UNARY_EXPR) print_token(cxt->pr, "(");
        print_token(cxt->pr, buf);
        if (pri > UNARY_EXPR) print_token(cxt->pr, ")");

    } else if (term->type->int_data.is_signed
               && term->int_literal.data[0] == '-') {
        num = -num;
        sprintf(buf,
                "-INT%d_C(%" PRIu64 ")",
                term->type->int_data.num_bits,
                num);
        if (pri > UNARY_EXPR) print_token(cxt->pr, "(");
        print_token(cxt->pr, buf);
        if (pri > UNARY_EXPR) print_token(cxt->pr, ")");

    } else {
        sprintf(buf,
                "%sINT%d_C(%s)",
                term->type->int_data.is_signed ? "" : "U",
                term->type->int_data.num_bits,
                term->int_literal.data);
        if (pri > POSTFIX_EXPR) print_token(cxt->pr, "(");
        print_token(cxt->pr, buf);
        if (pri > POSTFIX_EXPR) print_token(cxt->pr, ")");
    }
}

static void codegen_string_literal(struct CGContext *cxt,
                                   enum Priority pri,
                                   enum TermMode mode,
                                   struct Term *term)
{
    // Currently string literals are TY_DYNAMIC_ARRAY, hence we need to create
    // a descriptor here.

    // Make the raw array of bytes
    char raw_array[TEMP_NAME_LEN];
    get_temp_name(cxt, raw_array);
    begin_item(cxt->pr);
    print_token(cxt->pr, "static");
    print_token(cxt->pr, "const");
    print_token(cxt->pr, "uint8_t");
    print_token(cxt->pr, raw_array);
    print_token(cxt->pr, "[]");
    print_token(cxt->pr, "=");
    print_token(cxt->pr, "{");

    for (uint32_t i = 0; i < term->string_literal.length; ++i) {
        if (i != 0) print_token(cxt->pr, ",");
        char buf[10];
        sprintf(buf, "%" PRIu8, term->string_literal.data[i]);
        print_token(cxt->pr, buf);
    }

    print_token(cxt->pr, "}");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    // Make a pointer to the first byte of the raw array
    char pointer[TEMP_NAME_LEN];
    get_temp_name(cxt, pointer);
    begin_item(cxt->pr);
    print_token(cxt->pr, "void");
    print_token(cxt->pr, "*");
    print_token(cxt->pr, pointer);
    print_token(cxt->pr, "=");
    print_token(cxt->pr, "(void*)");
    print_token(cxt->pr, raw_array);
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    // Make a constant giving the array size
    char string_length[TEMP_NAME_LEN];
    get_temp_name(cxt, string_length);
    begin_item(cxt->pr);
    print_token(cxt->pr, "uint64_t");
    print_token(cxt->pr, string_length);
    print_token(cxt->pr, "=");
    char buf[30];
    sprintf(buf, "%" PRIu32, term->string_literal.length);
    print_token(cxt->pr, buf);
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    // Make the descriptor
    char descr[TEMP_NAME_LEN];
    make_temporary(cxt, descr, term->type);

    begin_item(cxt->pr);
    print_token(cxt->pr, "memcpy");
    print_token(cxt->pr, "(");
    print_token(cxt->pr, descr);
    print_token(cxt->pr, ",");
    print_token(cxt->pr, "&");
    print_token(cxt->pr, pointer);
    print_token(cxt->pr, ",");
    print_token(cxt->pr, "sizeof(void*)");
    print_token(cxt->pr, ")");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    print_token(cxt->pr, "memcpy");
    print_token(cxt->pr, "(");
    print_token(cxt->pr, descr);
    print_token(cxt->pr, "+");
    print_token(cxt->pr, "sizeof(void*)");
    print_token(cxt->pr, ",");
    print_token(cxt->pr, "&");
    print_token(cxt->pr, string_length);
    print_token(cxt->pr, ",");
    print_token(cxt->pr, "8");
    print_token(cxt->pr, ")");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    // Return the descriptor
    print_token(cxt->pr, descr);
}

static void codegen_cast(struct CGContext *cxt,
                         enum Priority pri,
                         enum TermMode mode,
                         struct Term *term)
{
    // Casting currently only works with scalar types so MODE_ADDR is unexpected here
    if (mode != MODE_VALUE) fatal_error("unexpected: MODE_ADDR in codegen_cast");

    if (pri > CAST_EXPR) print_token(cxt->pr, "(");

    print_token(cxt->pr, "(");
    codegen_type(cxt, term->cast.target_type);
    print_token(cxt->pr, ")");

    codegen_term(cxt, CAST_EXPR, MODE_VALUE, term->cast.operand);

    if (pri > CAST_EXPR) print_token(cxt->pr, ")");
}

static void codegen_if(struct CGContext *cxt,
                       enum Priority pri,
                       enum TermMode mode,
                       struct Term *term)
{
    char name[TEMP_NAME_LEN];
    make_temporary(cxt, name, term->type);

    begin_item(cxt->pr);
    print_token(cxt->pr, "if");
    print_token(cxt->pr, "(");
    codegen_term(cxt, EXPR, MODE_VALUE, term->if_data.cond);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, "{");
    new_line(cxt->pr);
    end_item(cxt->pr);

    increase_indent(cxt->pr);
    copy_term_to_variable(cxt, name, false, term->if_data.then_branch);

    decrease_indent(cxt->pr);
    begin_item(cxt->pr);
    print_token(cxt->pr, "}");
    print_token(cxt->pr, "else");
    print_token(cxt->pr, "{");
    new_line(cxt->pr);
    end_item(cxt->pr);

    increase_indent(cxt->pr);
    copy_term_to_variable(cxt, name, false, term->if_data.else_branch);

    decrease_indent(cxt->pr);
    begin_item(cxt->pr);
    print_token(cxt->pr, "}");
    new_line(cxt->pr);
    end_item(cxt->pr);

    print_token(cxt->pr, name);
}

static void codegen_unop(struct CGContext *cxt,
                         enum Priority pri,
                         enum TermMode mode,
                         struct Term *term)
{
    if (mode != MODE_VALUE) fatal_error("unexpected: MODE_ADDR in codegen_unop");

    if (pri > UNARY_EXPR) print_token(cxt->pr, "(");

    switch (term->unop.operator) {
    case UNOP_NEGATE: print_token(cxt->pr, "-"); break;
    case UNOP_COMPLEMENT: print_token(cxt->pr, "~"); break;
    case UNOP_NOT: print_token(cxt->pr, "!"); break;
    default: fatal_error("Unknown unop");
    }

    codegen_term(cxt, CAST_EXPR, MODE_VALUE, term->unop.operand);

    if (pri > UNARY_EXPR) print_token(cxt->pr, ")");
}

static void short_circuit_binop(struct CGContext *cxt,
                                enum Priority pri,
                                struct Term *term)
{
    // a && b   -->   result = a;  if (result)  result = b;
    // a || b   -->   result = a;  if (!result) result = b;
    // a ==> b  -->   result = !a; if (!result) result = b;

    char name[TEMP_NAME_LEN];
    get_temp_name(cxt, name);

    begin_item(cxt->pr);
    print_token(cxt->pr, "uint8_t");
    print_token(cxt->pr, name);
    print_token(cxt->pr, "=");

    if (term->binop.list->operator == BINOP_IMPLIES) {
        print_token(cxt->pr, "!");
        codegen_term(cxt, CAST_EXPR, MODE_VALUE, term->binop.lhs);
    } else {
        codegen_term(cxt, ASSIGN_EXPR, MODE_VALUE, term->binop.lhs);
    }
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    begin_item(cxt->pr);
    print_token(cxt->pr, "if");
    print_token(cxt->pr, "(");
    if (term->binop.list->operator != BINOP_AND) print_token(cxt->pr, "!");
    print_token(cxt->pr, name);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, "{");
    new_line(cxt->pr);
    end_item(cxt->pr);

    increase_indent(cxt->pr);
    copy_term_to_variable(cxt, name, false, term->binop.list->rhs);

    decrease_indent(cxt->pr);
    begin_item(cxt->pr);
    print_token(cxt->pr, "}");
    new_line(cxt->pr);
    end_item(cxt->pr);

    print_token(cxt->pr, name);
}

static void shift_binop(struct CGContext *cxt,
                        enum Priority pri,
                        struct Term *term)
{
    if (term->type->tag != TY_FINITE_INT) fatal_error("shift_binop: unexpected type");

    if (!term->type->int_data.is_signed) {
        // If E1 is an unsigned type then the behaviour of both E1 << E2 and
        // E1 >> E2 are well defined by the C standard.
        // The only gotcha is that E1 might be promoted to a signed integer type
        // by the integer promotion rules. To counteract this, one can add 0u
        // (not 0) to it. This forces it to promote to "unsigned int" if it
        // promotes at all.

        // Generate (E1 + 0u) << E2  (or >>).
        // This is a shift-expression so will require parens in a context
        // of priority higher than SHIFT_EXPR.
        if (pri > SHIFT_EXPR) print_token(cxt->pr, "(");
        print_token(cxt->pr, "(");
        codegen_term(cxt, ADD_EXPR, MODE_VALUE, term->binop.lhs);
        print_token(cxt->pr, "+");
        print_token(cxt->pr, "0u");
        print_token(cxt->pr, ")");
        print_token(cxt->pr, term->binop.list->operator == BINOP_SHIFTLEFT ? "<<" : ">>");

        // technically this should be ADD_EXPR, but MULT_EXPR will prevent some
        // compiler warnings
        codegen_term(cxt, MULT_EXPR, MODE_VALUE, term->binop.list->rhs);

        if (pri > SHIFT_EXPR) print_token(cxt->pr, ")");

    } else if (term->binop.list->operator == BINOP_SHIFTRIGHT) {
        // Right-shifting a signed value.
        // This is implementation-defined behaviour, but according to our assumptions
        // (listed at the top of this file) we assume that the C compiler will do
        // an arithmetic right shift in this case.

        // NOTE: If we wanted to drop this assumption, we could try one of the
        // approaches listed here:
        // https://stackoverflow.com/questions/31879878/how-can-i-perform-arithmetic-right-shift-in-c-in-a-portable-way

        // Generate E1 >> E2 (we do not have to worry about promotions in this case
        // as the promotion would be to another signed type).
        if (pri > SHIFT_EXPR) print_token(cxt->pr, "(");

        // technically this should be SHIFT_EXPR, but using MULT_EXPR will prevent
        // some compiler warnings
        codegen_term(cxt, MULT_EXPR, MODE_VALUE, term->binop.lhs);

        print_token(cxt->pr, ">>");
        codegen_term(cxt, ADD_EXPR, MODE_VALUE, term->binop.list->rhs);
        if (pri > SHIFT_EXPR) print_token(cxt->pr, ")");

    } else {
        // Left-shifting a signed value.
        // This is *undefined* behaviour (if the value is negative) so we had better
        // not do it.
        // Instead we can cast the value to the corresponding unsigned type
        // (this is well-defined, wrapping around if the value is out of range),
        // add 0u to prevent promotion to a signed type,
        // do the shift,
        // and memcpy back to a signed value.
        // (memcpy is required rather than just a cast, because casting to a
        // signed type is undefined, or at least implementation-defined, if the
        // value is out of range. But the compiler should be able to optimise away the
        // memcpy.)

        // uintN_t temp;
        char temp_name[TEMP_NAME_LEN];
        struct Type dummy_type = *(term->type);
        dummy_type.int_data.is_signed = false;
        make_temporary(cxt, temp_name, &dummy_type);

        // temp = ((uintN_t)E1 + 0u) << E2;
        begin_item(cxt->pr);
        print_token(cxt->pr, temp_name);
        print_token(cxt->pr, "=");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, "(");
        codegen_type(cxt, &dummy_type);
        print_token(cxt->pr, ")");
        codegen_term(cxt, CAST_EXPR, MODE_VALUE, term->binop.lhs);
        print_token(cxt->pr, "+");
        print_token(cxt->pr, "0u");
        print_token(cxt->pr, ")");
        print_token(cxt->pr, "<<");

        // technically this should be ADD_EXPR, but using MULT_EXPR will prevent
        // some compiler warnings
        codegen_term(cxt, MULT_EXPR, MODE_VALUE, term->binop.list->rhs);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        // intN_t result;
        char result_name[TEMP_NAME_LEN];
        make_temporary(cxt, result_name, term->type);

        // memcpy(&result, &temp, SIZE);
        begin_item(cxt->pr);
        print_token(cxt->pr, "memcpy");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, "&");
        print_token(cxt->pr, result_name);
        print_token(cxt->pr, ",");
        print_token(cxt->pr, "&");
        print_token(cxt->pr, temp_name);
        print_token(cxt->pr, ",");
        print_size_of_type(cxt, ASSIGN_EXPR, term->type);
        print_token(cxt->pr, ")");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        print_token(cxt->pr, result_name);
    }
}

static void codegen_binop(struct CGContext *cxt,
                          enum Priority pri,
                          enum TermMode mode,
                          struct Term *term)
{
    if (mode != MODE_VALUE) fatal_error("unexpected: MODE_ADDR in codegen_binop");

    enum BinOp binop = term->binop.list->operator;

    enum Priority expr_type;
    enum Priority lhs_type;
    enum Priority rhs_type;

    switch (binop) {
    case BINOP_AND:
    case BINOP_OR:
    case BINOP_IMPLIES:
        // These need special handling
        short_circuit_binop(cxt, pri, term);
        return;

    case BINOP_SHIFTLEFT:
    case BINOP_SHIFTRIGHT:
        // These also need special handling because the standard doesn't fully
        // define what these operators do in all cases!
        // (In particular: left shifting a negative value is undefined behaviour,
        // and right shifting a negative value is implementation-defined behaviour.)
        shift_binop(cxt, pri, term);
        return;

    case BINOP_PLUS:
    case BINOP_MINUS:
        expr_type = ADD_EXPR;
        lhs_type = ADD_EXPR;
        rhs_type = MULT_EXPR;
        break;

    case BINOP_TIMES:
    case BINOP_DIVIDE:
    case BINOP_MODULO:
        expr_type = MULT_EXPR;
        lhs_type = MULT_EXPR;
        rhs_type = CAST_EXPR;
        break;

    case BINOP_BITAND:
        expr_type = BIT_AND_EXPR;
        // technically lhs_type should be BIT_AND_EXPR and rhs_type should be
        // EQ_EXPR, but compilers often give warnings so we use CAST_EXPR instead
        // (this results in more parens than strictly required, but is safe)
        lhs_type = CAST_EXPR;
        rhs_type = CAST_EXPR;
        break;

    case BINOP_BITOR:
        expr_type = BIT_OR_EXPR;
        lhs_type = CAST_EXPR;
        rhs_type = CAST_EXPR;
        break;

    case BINOP_BITXOR:
        expr_type = BIT_XOR_EXPR;
        lhs_type = CAST_EXPR;
        rhs_type = CAST_EXPR;
        break;

    case BINOP_EQUAL:
    case BINOP_NOT_EQUAL:
        expr_type = EQ_EXPR;
        lhs_type = EQ_EXPR;
        rhs_type = REL_EXPR;
        break;

    case BINOP_LESS:
    case BINOP_LESS_EQUAL:
    case BINOP_GREATER:
    case BINOP_GREATER_EQUAL:
        expr_type = REL_EXPR;
        lhs_type = REL_EXPR;
        rhs_type = SHIFT_EXPR;
        break;

    case BINOP_IMPLIED_BY:
        fatal_error("should have been removed by typechecker");

    case BINOP_IFF:
        // same as == for booleans
        expr_type = EQ_EXPR;
        lhs_type = EQ_EXPR;
        rhs_type = REL_EXPR;
        break;

    default:
        fatal_error("unrecognised binop");
    }

    if (pri > expr_type) print_token(cxt->pr, "(");

    codegen_term(cxt, lhs_type, MODE_VALUE, term->binop.lhs);

    const char *str;
    switch (binop) {
    case BINOP_PLUS: str = "+"; break;
    case BINOP_MINUS: str = "-"; break;
    case BINOP_TIMES: str = "*"; break;
    case BINOP_DIVIDE: str = "/"; break;
    case BINOP_MODULO: str = "%"; break;
    case BINOP_BITAND: str = "&"; break;
    case BINOP_BITOR: str = "|"; break;
    case BINOP_BITXOR: str = "^"; break;

    case BINOP_EQUAL: case BINOP_IFF: str = "=="; break;
    case BINOP_NOT_EQUAL: str = "!="; break;
    case BINOP_LESS: str = "<"; break;
    case BINOP_LESS_EQUAL: str = "<="; break;
    case BINOP_GREATER: str = ">"; break;
    case BINOP_GREATER_EQUAL: str = ">="; break;

    case BINOP_AND:
    case BINOP_OR:
    case BINOP_IMPLIES:
    case BINOP_IMPLIED_BY:
    case BINOP_SHIFTLEFT:
    case BINOP_SHIFTRIGHT:
        fatal_error("unreachable");
    }

    print_token(cxt->pr, str);

    codegen_term(cxt, rhs_type, MODE_VALUE, term->binop.list->rhs);

    if (pri > expr_type) print_token(cxt->pr, ")");
}

static void codegen_let(struct CGContext *cxt,
                        enum Priority pri,
                        enum TermMode mode,
                        struct Term *term)
{
    char temp_name[TEMP_NAME_LEN];
    get_temp_name(cxt, temp_name);

    begin_item(cxt->pr);
    codegen_type(cxt, term->let.rhs->type);
    char *mangled_name = mangle_name(term->let.name);
    print_token(cxt->pr, mangled_name);
    free(mangled_name);
    print_token(cxt->pr, "=");
    codegen_term(cxt, ASSIGN_EXPR, MODE_VALUE, term->let.rhs);
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    codegen_term(cxt, pri, mode, term->let.body);
}

static const char * get_function_name(struct Term *term)
{
    if (term->tag != TM_CALL) fatal_error("get_function_name: TM_CALL is required");

    if (term->call.func->tag == TM_VAR) {
        return term->call.func->var.name;
    } else if (term->call.func->tag == TM_TYAPP
               && term->call.func->tyapp.lhs->tag == TM_VAR) {
        return term->call.func->tyapp.lhs->var.name;
    } else {
        fatal_error("get_function_name: couldn't obtain function name");
    }
}

static struct Type * get_function_type(struct Term *term)
{
    if (term->tag != TM_CALL) fatal_error("get_function_type: TM_CALL is required");

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

// This can be used for both terms and statements.
static void codegen_call(struct CGContext *cxt,
                         enum Priority pri,
                         struct Term *term,
                         bool as_statement)
{
    const char * fun_name = get_function_name(term);
    struct Type * fun_ty = get_function_type(term);
    struct Type * ret_ty = fun_ty->function_data.return_type;

    // Make a temporary buffer to hold the return value, if required.
    char ret_name[TEMP_NAME_LEN];
    bool using_ret_buffer = false;
    if (ret_ty && !is_scalar_type(cxt, ret_ty)) {
        make_temporary(cxt, ret_name, term->type);
        using_ret_buffer = true;
    }

    // Is this call going to be directly used in an expression?
    bool call_expr = !using_ret_buffer && !as_statement;

    // Parenthesise the expression if necessary
    if (call_expr && pri > POSTFIX_EXPR) print_token(cxt->pr, "(");

    // Begin a new item if necessary
    if (!call_expr) begin_item(cxt->pr);

    // Write the function name.
    struct CodegenEntry *entry = hash_table_lookup(cxt->env, fun_name);
    if (entry && entry->foreign_name) {
        print_token(cxt->pr, entry->foreign_name);
    } else {
        char *mangled_name = mangle_name(fun_name);
        print_token(cxt->pr, mangled_name);
        free(mangled_name);
    }

    print_token(cxt->pr, "(");
    bool first_arg = true;

    // Write the return argument, if necessary
    if (using_ret_buffer) {
        if (is_scalar_type(cxt, term->type) && !is_scalar_type(cxt, ret_ty)) {
            print_token(cxt->pr, "(");
            print_token(cxt->pr, "char");
            print_token(cxt->pr, "*");
            print_token(cxt->pr, ")");
            print_token(cxt->pr, "&");
        }
        print_token(cxt->pr, ret_name);
        first_arg = false;
    }

    // Write the generic size arguments
    if (term->call.func->tag == TM_TYAPP) {
        for (struct TypeList *tyarg = term->call.func->tyapp.tyargs; tyarg; tyarg = tyarg->next) {
            if (!first_arg) {
                print_token(cxt->pr, ",");
            } else {
                first_arg = false;
            }
            print_size_of_type(cxt, ASSIGN_EXPR, tyarg->type);
        }
    }

    // Write the actual arguments
    struct FunArg *formal = fun_ty->function_data.args;
    struct OpTermList *actual = term->call.args;
    for (; actual; actual = actual->next, formal = formal->next) {
        if (!first_arg) {
            print_token(cxt->pr, ",");
        } else {
            first_arg = false;
        }
        enum TermMode arg_mode;
        if (is_scalar_type(cxt, formal->type) && !formal->ref) {
            arg_mode = MODE_VALUE;
        } else {
            arg_mode = MODE_ADDR;
        }
        codegen_term(cxt, ASSIGN_EXPR, arg_mode, actual->rhs);
    }

    print_token(cxt->pr, ")");

    // Finish up
    if (call_expr && pri > POSTFIX_EXPR) print_token(cxt->pr, ")");
    if (!call_expr) {
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);
        if (!as_statement) {
            print_token(cxt->pr, ret_name);
        }
    }
}

static void codegen_record(struct CGContext *cxt,
                           enum Priority pri,
                           enum TermMode mode,
                           struct Term *term)
{
    char result_name[TEMP_NAME_LEN];
    make_temporary(cxt, result_name, term->type);

    struct SizeExpr *offset = zero_size_expr();

    for (struct NameTermList *field = term->record.fields; field; field = field->next) {
        // Using memcpy is fine here as the existing term cannot possibly overlap
        // with our newly-created "result" variable.

        struct SizeExpr *size = get_size_of_type(cxt, field->term->type);

        begin_item(cxt->pr);
        print_token(cxt->pr, "memcpy");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, result_name);
        if (!is_size_expr_zero(offset)) {
            print_token(cxt->pr, "+");
            print_size_expr(cxt, ADD_EXPR, offset);
        }
        print_token(cxt->pr, ",");
        codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, field->term);
        print_token(cxt->pr, ",");
        print_size_expr(cxt, ASSIGN_EXPR, size);
        print_token(cxt->pr, ")");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        struct SizeExpr *new_offset = add_size_expr(offset, size);
        free_size_expr(size);
        free_size_expr(offset);
        offset = new_offset;
    }

    free_size_expr(offset);

    print_token(cxt->pr, result_name);
}

static void codegen_record_update(struct CGContext *cxt,
                                  enum Priority pri,
                                  enum TermMode mode,
                                  struct Term *term)
{
    char result_name[TEMP_NAME_LEN];
    make_temporary(cxt, result_name, term->type);
    copy_term_to_variable(cxt, result_name, false, term->record_update.lhs);

    for (struct NameTermList *field = term->record_update.fields; field; field = field->next) {
        struct SizeExpr *offset = get_field_offset(cxt, term->type, field->name);

        // Using memcpy (as opposed to memmove) is fine here, as the existing terms
        // cannot overlap with result_name
        begin_item(cxt->pr);
        print_token(cxt->pr, "memcpy");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, result_name);
        if (!is_size_expr_zero(offset)) {
            print_token(cxt->pr, "+");
            print_size_expr(cxt, ADD_EXPR, offset);
        }
        print_token(cxt->pr, ",");
        codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, field->term);
        print_token(cxt->pr, ",");
        print_size_of_type(cxt, ASSIGN_EXPR, field->term->type);
        print_token(cxt->pr, ")");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        free_size_expr(offset);
    }

    print_token(cxt->pr, result_name);
}

static void codegen_term_plus_offset(struct CGContext *cxt,
                                     enum Priority pri,
                                     struct Term *base_addr,
                                     struct SizeExpr *offset)
{
    if (pri > ADD_EXPR) print_token(cxt->pr, "(");
    codegen_term(cxt, ADD_EXPR, MODE_ADDR, base_addr); // generates a char*
    if (!is_size_expr_zero(offset)) {
        print_token(cxt->pr, "+");
        print_size_expr(cxt, ADD_EXPR, offset);
    }
    if (pri > ADD_EXPR) print_token(cxt->pr, ")");
}

static void codegen_field_proj(struct CGContext *cxt,
                               enum Priority pri,
                               enum TermMode mode,
                               struct Term *term)
{
    struct SizeExpr *offset = get_field_offset(cxt,
                                               term->field_proj.lhs->type,
                                               term->field_proj.field_name);

    if (is_scalar_type(cxt, term->type) && mode == MODE_VALUE) {
        // we need to memcpy the field into a temporary scalar variable, then
        // return that variable
        char name[TEMP_NAME_LEN];
        make_temporary(cxt, name, term->type);

        begin_item(cxt->pr);
        print_token(cxt->pr, "memcpy");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, "&");
        print_token(cxt->pr, name);
        print_token(cxt->pr, ",");
        codegen_term_plus_offset(cxt, ASSIGN_EXPR, term->field_proj.lhs, offset);
        print_token(cxt->pr, ",");
        print_size_of_type(cxt, ASSIGN_EXPR, term->type);
        print_token(cxt->pr, ")");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        print_token(cxt->pr, name);

    } else {
        // we can just return a pointer to the field
        codegen_term_plus_offset(cxt, pri, term->field_proj.lhs, offset);
    }

    free_size_expr(offset);
}

static void codegen_variant(struct CGContext *cxt,
                            enum Priority pri,
                            enum TermMode mode,
                            struct Term *term)
{
    char result_name[TEMP_NAME_LEN];
    make_temporary(cxt, result_name, term->type);

    const char *tag_type;
    int tag_size = get_tag_size(term->type, &tag_type);

    char tag_name[TEMP_NAME_LEN];
    get_temp_name(cxt, tag_name);

    uint32_t tag_num = get_tag_number_and_payload_type(term->type,
                                                       term->variant.variant_name,
                                                       NULL);

    char buf[20];

    begin_item(cxt->pr);
    print_token(cxt->pr, tag_type);
    print_token(cxt->pr, tag_name);
    print_token(cxt->pr, "=");
    sprintf(buf, "%" PRIu32, tag_num);
    print_token(cxt->pr, buf);
    print_token(cxt->pr, ";");
    new_line(cxt->pr);

    print_token(cxt->pr, "memcpy");
    print_token(cxt->pr, "(");
    print_token(cxt->pr, result_name);
    print_token(cxt->pr, ",");
    print_token(cxt->pr, "&");
    print_token(cxt->pr, tag_name);
    print_token(cxt->pr, ",");
    sprintf(buf, "%d", tag_size);
    print_token(cxt->pr, buf);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);

    print_token(cxt->pr, "memcpy");
    print_token(cxt->pr, "(");
    print_token(cxt->pr, result_name);
    print_token(cxt->pr, "+");
    print_token(cxt->pr, buf);  // buf still contains tag_size
    print_token(cxt->pr, ",");
    codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, term->variant.payload);
    print_token(cxt->pr, ",");
    print_size_of_type(cxt, ASSIGN_EXPR, term->variant.payload->type);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    print_token(cxt->pr, result_name);
}

// This can be used for both terms and statements.
// Note: after typechecking, MATCH is only used for variants, not integers or
// anything else.
static void codegen_match(struct CGContext *cxt,
                          struct Term *scrut,
                          struct Arm *arms,
                          bool as_statement)
{
    struct Type *variant_type = scrut->type;

    // Get a char* pointer to the scrutinee.
    char scrut_ptr_name[TEMP_NAME_LEN];
    get_temp_name(cxt, scrut_ptr_name);

    begin_item(cxt->pr);
    print_token(cxt->pr, "char");
    print_token(cxt->pr, "*");
    print_token(cxt->pr, scrut_ptr_name);
    print_token(cxt->pr, "=");
    codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, scrut);
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    // Read out the tag.
    char tag_name[TEMP_NAME_LEN];
    get_temp_name(cxt, tag_name);

    const char *tag_type_name;
    int tag_size = get_tag_size(variant_type, &tag_type_name);
    begin_item(cxt->pr);
    print_token(cxt->pr, tag_type_name);
    print_token(cxt->pr, tag_name);
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    print_token(cxt->pr, "memcpy");
    print_token(cxt->pr, "(");
    print_token(cxt->pr, "&");
    print_token(cxt->pr, tag_name);
    print_token(cxt->pr, ",");
    print_token(cxt->pr, scrut_ptr_name);
    print_token(cxt->pr, ",");
    char buf[20];
    sprintf(buf, "%d", tag_size);
    print_token(cxt->pr, buf);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);

    // If this is an expression, create a variable to hold the result.
    // NB there must be at least one Arm for match expressions.
    char result_name[TEMP_NAME_LEN];
    if (!as_statement) {
        struct Term *first_rhs = (struct Term*) arms->rhs;
        make_temporary(cxt, result_name, first_rhs->type);
    }

    // Write the switch statement
    begin_item(cxt->pr);
    print_token(cxt->pr, "switch");
    print_token(cxt->pr, "(");
    print_token(cxt->pr, tag_name);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, "{");
    new_line(cxt->pr);
    end_item(cxt->pr);

    for (struct Arm *arm = arms; arm; arm = arm->next) {
        char *copied_name = NULL;
        struct CodegenEntry *entry = NULL;

        switch (arm->pattern->tag) {
        case PAT_VARIANT:
            {
                struct Type *payload_type;
                uint32_t tag = get_tag_number_and_payload_type(
                    variant_type,
                    arm->pattern->variant.variant_name,
                    &payload_type);
                sprintf(buf, "%" PRIu32, tag);

                begin_item(cxt->pr);
                print_token(cxt->pr, "case");
                print_token(cxt->pr, buf);
                print_token(cxt->pr, ":");
                print_token(cxt->pr, "{");
                new_line(cxt->pr);
                end_item(cxt->pr);

                increase_indent(cxt->pr);

                switch (arm->pattern->variant.payload->tag) {
                case PAT_VAR:
                    {
                        // Make a variable for the payload...
                        begin_item(cxt->pr);
                        print_token(cxt->pr, "char");
                        print_token(cxt->pr, "*");
                        char *mangled_name = mangle_name(arm->pattern->variant.payload->var.name);
                        print_token(cxt->pr, mangled_name);
                        free(mangled_name);
                        print_token(cxt->pr, "=");
                        print_token(cxt->pr, scrut_ptr_name);
                        print_token(cxt->pr, "+");
                        sprintf(buf, "%d", tag_size);
                        print_token(cxt->pr, buf);
                        print_token(cxt->pr, ";");
                        new_line(cxt->pr);
                        end_item(cxt->pr);

                        // We will need a new CodegenEntry for the payload variable
                        entry = alloc(sizeof(struct CodegenEntry));
                        memset(entry, 0, sizeof(*entry));
                        entry->is_ref = true;
                        copied_name = copy_string(arm->pattern->variant.payload->var.name);
                        hash_table_insert(cxt->env, copied_name, entry);
                    }
                    break;

                case PAT_WILDCARD:
                    // do nothing
                    break;

                default:
                    fatal_error("unexpected pattern");
                }
            }
            break;

        case PAT_WILDCARD:
            begin_item(cxt->pr);
            print_token(cxt->pr, "default");
            print_token(cxt->pr, ":");
            print_token(cxt->pr, "{");
            new_line(cxt->pr);
            end_item(cxt->pr);
            increase_indent(cxt->pr);
            break;

        default:
            fatal_error("unexpected pattern");
        }

        // Now we are inside the "case" or "default", we can generate the payload
        // (either term or statements).
        if (as_statement) {
            codegen_statements(cxt, arm->rhs);
        } else {
            copy_term_to_variable(cxt, result_name, false, arm->rhs);
        }

        begin_item(cxt->pr);
        print_token(cxt->pr, "break");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        decrease_indent(cxt->pr);
        begin_item(cxt->pr);
        print_token(cxt->pr, "}");
        new_line(cxt->pr);
        end_item(cxt->pr);

        // Remove entry from CodegenEnv if required.
        if (entry) {
            hash_table_remove(cxt->env, copied_name);
            free(copied_name);
            free(entry);
        }
    }

    // Close the switch.
    begin_item(cxt->pr);
    print_token(cxt->pr, "}");
    new_line(cxt->pr);
    end_item(cxt->pr);

    // Finally, if this was an expression, return the result variable.
    if (!as_statement) {
        print_token(cxt->pr, result_name);
    }
}

static void codegen_sizeof(struct CGContext *cxt,
                           enum Priority pri,
                           enum TermMode mode,
                           struct Term *term)
{
    if (term->sizeof_data.rhs->type->tag == TY_DYNAMIC_ARRAY) {
        // This produces either a u64, or a tuple of u64s.
        // Either way, we can just memcpy directly from the descriptor.
        char name[TEMP_NAME_LEN];
        make_temporary(cxt, name, term->type);

        begin_item(cxt->pr);
        print_token(cxt->pr, "memcpy");
        print_token(cxt->pr, "(");
        if (term->type->tag == TY_FINITE_INT) print_token(cxt->pr, "&");
        print_token(cxt->pr, name);
        print_token(cxt->pr, ",");

        // 'rhs' is an array, therefore represented as a char* descriptor.
        // We add sizeof(void*) to get to the size.
        codegen_term(cxt, ADD_EXPR, MODE_VALUE, term->sizeof_data.rhs);
        print_token(cxt->pr, "+");
        print_token(cxt->pr, "sizeof(void*)");
        print_token(cxt->pr, ",");

        uint64_t bytes_to_copy = 8 * term->sizeof_data.rhs->type->dynamic_array_data.ndim;
        char buf[50];
        sprintf(buf, "%" PRIu64, bytes_to_copy);
        print_token(cxt->pr, buf);

        print_token(cxt->pr, ")");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        // Return the value that we just memcpy'd out.
        print_token(cxt->pr, name);

    } else if (term->sizeof_data.rhs->type->tag == TY_FIXED_ARRAY) {
        if (term->sizeof_data.rhs->type->fixed_array_data.ndim == 1) {
            // Just return the size directly as an integer literal
            uint64_t size = normal_form_to_int(term->sizeof_data.rhs->type->fixed_array_data.sizes[0]);
            char buf[50];
            sprintf(buf, "UINT64_C(%" PRIu64 ")", size);
            print_token(cxt->pr, buf);

        } else {
            // We need to make a little tuple
            char tuple[TEMP_NAME_LEN];
            make_temporary(cxt, tuple, term->type);

            char tmp[TEMP_NAME_LEN];
            get_temp_name(cxt, tmp);
            begin_item(cxt->pr);
            print_token(cxt->pr, "uint64_t");
            print_token(cxt->pr, tmp);
            print_token(cxt->pr, ";");
            new_line(cxt->pr);
            end_item(cxt->pr);

            for (int i = 0; i < term->sizeof_data.rhs->type->fixed_array_data.ndim; ++i) {
                begin_item(cxt->pr);
                print_token(cxt->pr, tmp);
                print_token(cxt->pr, "=");

                uint64_t size = normal_form_to_int(term->sizeof_data.rhs->type->fixed_array_data.sizes[i]);
                char buf[50];
                sprintf(buf, "UINT64_C(%" PRIu64 ");", size);
                print_token(cxt->pr, buf);

                new_line(cxt->pr);
                print_token(cxt->pr, "memcpy");
                print_token(cxt->pr, "(");
                print_token(cxt->pr, tuple);
                if (i != 0) {
                    print_token(cxt->pr, "+");
                    sprintf(buf, "%d", i*8);
                    print_token(cxt->pr, buf);
                }
                print_token(cxt->pr, ",");
                print_token(cxt->pr, "&");
                print_token(cxt->pr, tmp);
                print_token(cxt->pr, ",");
                print_token(cxt->pr, "8");  // sizeof(uint64_t)
                print_token(cxt->pr, ")");
                print_token(cxt->pr, ";");
                new_line(cxt->pr);
                end_item(cxt->pr);
            }

            print_token(cxt->pr, tuple);
        }

    } else {
        fatal_error("codegen_sizeof: wrong type");
    }
}

static void print_pointer_to_element(struct CGContext *cxt,
                                     enum Priority pri,
                                     struct Term *array_term,
                                     struct OpTermList *indexes)
{
    if (pri > ADD_EXPR) print_token(cxt->pr, "(");

    if (array_term->type->tag == TY_FIXED_ARRAY) {
        codegen_term(cxt, ADD_EXPR, MODE_VALUE, array_term);
        print_token(cxt->pr, "+");

        print_size_of_type(cxt, MULT_EXPR, array_term->type->fixed_array_data.element_type);
        print_token(cxt->pr, "*");
        print_token(cxt->pr, "(");

        // array[x,y,z] becomes:
        // base_ptr + element_size * (x + ndim0 * (y + ndim1 * (z)))
        // Note this gives "column major" (i.e. Fortran-style) indexing.
        struct Term **sizes = array_term->type->fixed_array_data.sizes;
        struct OpTermList *index = indexes;
        while (index) {
            codegen_term(cxt, ADD_EXPR, MODE_VALUE, index->rhs);
            if (index->next) {
                print_token(cxt->pr, "+");
                char buf[40];
                uint64_t size = normal_form_to_int(*sizes);
                sprintf(buf, "%" PRIu64, size);
                print_token(cxt->pr, buf);
                print_token(cxt->pr, "*");
                print_token(cxt->pr, "(");
            }
            index = index->next;
            ++sizes;
        }
        for (int i = 0; i < array_term->type->fixed_array_data.ndim; ++i) {
            print_token(cxt->pr, ")");
        }

    } else {
        char descriptor[TEMP_NAME_LEN];
        get_temp_name(cxt, descriptor);
        begin_item(cxt->pr);
        print_token(cxt->pr, "char");
        print_token(cxt->pr, "*");
        print_token(cxt->pr, descriptor);
        print_token(cxt->pr, "=");
        codegen_term(cxt, ASSIGN_EXPR, MODE_VALUE, array_term);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);

        char base_ptr[TEMP_NAME_LEN];
        get_temp_name(cxt, base_ptr);
        print_token(cxt->pr, "char");
        print_token(cxt->pr, "*");
        print_token(cxt->pr, base_ptr);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        print_token(cxt->pr, "memcpy");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, "&");
        print_token(cxt->pr, base_ptr);
        print_token(cxt->pr, ",");
        print_token(cxt->pr, descriptor);
        print_token(cxt->pr, ",");
        print_token(cxt->pr, "sizeof(void*)");
        print_token(cxt->pr, ")");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);

        print_token(cxt->pr, base_ptr);
        print_token(cxt->pr, "+");

        print_size_of_type(cxt, MULT_EXPR, array_term->type->dynamic_array_data.element_type);
        print_token(cxt->pr, "*");
        print_token(cxt->pr, "(");

        // Same as above, but more complicated because we have to read out each
        // dimension with a memcpy, instead of just getting it from the array type.
        struct OpTermList *index = indexes;
        uint64_t dim_offset = 0;
        while (index) {
            codegen_term(cxt, ADD_EXPR, MODE_VALUE, index->rhs);
            if (index->next) {
                print_token(cxt->pr, "+");

                char size_name[TEMP_NAME_LEN];
                get_temp_name(cxt, size_name);
                begin_item(cxt->pr);
                print_token(cxt->pr, "uint64_t");
                print_token(cxt->pr, size_name);
                print_token(cxt->pr, ";");
                new_line(cxt->pr);
                print_token(cxt->pr, "memcpy");
                print_token(cxt->pr, "(");
                print_token(cxt->pr, "&");
                print_token(cxt->pr, size_name);
                print_token(cxt->pr, ",");
                print_token(cxt->pr, descriptor);
                print_token(cxt->pr, "+");
                print_token(cxt->pr, "sizeof(void*)");

                if (dim_offset != 0) {
                    print_token(cxt->pr, "+");
                    char buf[40];
                    sprintf(buf, "%" PRIu64, dim_offset);
                    print_token(cxt->pr, buf);
                }

                dim_offset += 8;

                print_token(cxt->pr, ",");
                print_token(cxt->pr, "8");
                print_token(cxt->pr, ")");
                print_token(cxt->pr, ";");
                new_line(cxt->pr);
                end_item(cxt->pr);

                print_token(cxt->pr, size_name);
                print_token(cxt->pr, "*");
                print_token(cxt->pr, "(");
            }

            index = index->next;
        }
        for (int i = 0; i < array_term->type->dynamic_array_data.ndim; ++i) {
            print_token(cxt->pr, ")");
        }
    }

    if (pri > ADD_EXPR) print_token(cxt->pr, ")");
}

static void codegen_array_proj(struct CGContext *cxt,
                               enum Priority pri,
                               enum TermMode mode,
                               struct Term *term)
{
    if (mode == MODE_ADDR || !is_scalar_type(cxt, term->type)) {
        print_pointer_to_element(cxt, pri, term->array_proj.lhs, term->array_proj.indexes);
    } else {
        char result[TEMP_NAME_LEN];
        make_temporary(cxt, result, term->type);
        begin_item(cxt->pr);
        print_token(cxt->pr, "memcpy");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, "&");
        print_token(cxt->pr, result);
        print_token(cxt->pr, ",");
        print_pointer_to_element(cxt, ASSIGN_EXPR, term->array_proj.lhs, term->array_proj.indexes);
        print_token(cxt->pr, ",");
        print_size_of_type(cxt, ASSIGN_EXPR, term->type);
        print_token(cxt->pr, ")");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        end_item(cxt->pr);
        print_token(cxt->pr, result);
    }
}

static void codegen_term(struct CGContext *cxt,
                         enum Priority pri,
                         enum TermMode mode,
                         struct Term *term)
{
    if (is_scalar_type(cxt, term->type) && mode == MODE_ADDR && !is_lvalue(term)) {
        // Someone has asked for the address of a non-lvalue scalar term
        // (like "1 + 2"). We will compute it to a temporary and give them the
        // address of the temporary (cast to char*).
        char name[TEMP_NAME_LEN];
        make_temporary(cxt, name, term->type);
        copy_term_to_variable(cxt, name, false, term);
        if (pri > CAST_EXPR) print_token(cxt->pr, "(");
        print_token(cxt->pr, "(");
        print_token(cxt->pr, "char");
        print_token(cxt->pr, "*");
        print_token(cxt->pr, ")");
        print_token(cxt->pr, "&");
        print_token(cxt->pr, name);
        if (pri > CAST_EXPR) print_token(cxt->pr, ")");

    } else {
        switch (term->tag) {
        case TM_VAR: codegen_var(cxt, pri, mode, term); break;

        case TM_DEFAULT:
        case TM_MATCH_FAILURE:
            // (For now, a match failure just generates a default value
            // of that type. Perhaps we could have a mode where it
            // crashes the program instead)
            codegen_default(cxt, pri, mode, term); break;

        case TM_BOOL_LITERAL: codegen_bool_literal(cxt, pri, mode, term); break;
        case TM_INT_LITERAL: codegen_int_literal(cxt, pri, mode, term); break;
        case TM_STRING_LITERAL: codegen_string_literal(cxt, pri, mode, term); break;
        case TM_CAST: codegen_cast(cxt, pri, mode, term); break;
        case TM_IF: codegen_if(cxt, pri, mode, term); break;
        case TM_UNOP: codegen_unop(cxt, pri, mode, term); break;
        case TM_BINOP: codegen_binop(cxt, pri, mode, term); break;
        case TM_LET: codegen_let(cxt, pri, mode, term); break;
        case TM_QUANTIFIER: fatal_error("unexpected: trying to generate code for quantifier");
        case TM_CALL: codegen_call(cxt, pri, term, false); break;
        case TM_TYAPP: fatal_error("unexpected: trying to generate code for type-application");
        case TM_RECORD: codegen_record(cxt, pri, mode, term); break;
        case TM_RECORD_UPDATE: codegen_record_update(cxt, pri, mode, term); break;
        case TM_FIELD_PROJ: codegen_field_proj(cxt, pri, mode, term); break;
        case TM_VARIANT: codegen_variant(cxt, pri, mode, term); break;
        case TM_MATCH: codegen_match(cxt, term->match.scrutinee, term->match.arms, false); break;
        case TM_SIZEOF: codegen_sizeof(cxt, pri, mode, term); break;
        case TM_ALLOCATED: fatal_error("unexpected: codegen_term called on TM_ALLOCATED");
        case TM_ARRAY_PROJ: codegen_array_proj(cxt, pri, mode, term); break;
        }
    }
}


//
// Code generation for statements
//

static void codegen_statements(struct CGContext *cxt,
                               struct Statement *stmts);

static void codegen_var_decl_stmt(struct CGContext *cxt,
                                  struct Statement *stmt)
{
    char *mangled_name = mangle_name(stmt->var_decl.name);
    char *copied_name = NULL;
    struct CodegenEntry *entry = NULL;

    begin_item(cxt->pr);

    if (stmt->var_decl.ref) {
        print_token(cxt->pr, "char");
        print_token(cxt->pr, "*");
        print_token(cxt->pr, mangled_name);
        print_token(cxt->pr, "=");
        codegen_term(cxt, ASSIGN_EXPR, MODE_ADDR, stmt->var_decl.rhs);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);

        entry = alloc(sizeof(struct CodegenEntry));
        memset(entry, 0, sizeof(*entry));
        entry->is_ref = true;
        copied_name = copy_string(stmt->var_decl.name);
        hash_table_insert(cxt->env, copied_name, entry);

    } else {
        declare_variable(cxt, mangled_name, stmt->var_decl.type, false);
        copy_term_to_variable(cxt, mangled_name, false, stmt->var_decl.rhs);
    }

    end_item(cxt->pr);

    free(mangled_name);

    codegen_statements(cxt, stmt->next);

    if (entry) {
        hash_table_remove(cxt->env, copied_name);
        free(copied_name);
        free(entry);
    }
}

static void codegen_assign_stmt(struct CGContext *cxt,
                                struct Statement *stmt)
{
    copy_term_to_term(cxt, stmt->assign.lhs, stmt->assign.rhs);
}

static void codegen_swap_stmt(struct CGContext *cxt,
                              struct Statement *stmt)
{
    char name[TEMP_NAME_LEN];
    make_temporary(cxt, name, stmt->swap.lhs->type);

    // temp = rhs; rhs = lhs; lhs = temp;
    copy_term_to_variable(cxt, name, false, stmt->swap.rhs);
    copy_term_to_term(cxt, stmt->swap.rhs, stmt->swap.lhs);
    copy_variable_to_term(cxt, stmt->swap.lhs, name);
}

static void codegen_return_stmt(struct CGContext *cxt,
                                struct Statement *stmt)
{
    begin_item(cxt->pr);

    if (stmt->ret.value) {
        if (is_scalar_type(cxt, stmt->ret.value->type)) {
            print_token(cxt->pr, "return");
            codegen_term(cxt, EXPR, MODE_VALUE, stmt->ret.value);
            print_token(cxt->pr, ";");
            new_line(cxt->pr);
        } else {
            copy_term_to_variable(cxt, "ret", false, stmt->ret.value);
            print_token(cxt->pr, "return");
            print_token(cxt->pr, ";");
            new_line(cxt->pr);
        }
    } else {
        print_token(cxt->pr, "return");
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
    }

    end_item(cxt->pr);
}

static void codegen_if_stmt(struct CGContext *cxt,
                            struct Statement *stmt)
{
    begin_item(cxt->pr);
    print_token(cxt->pr, "if");
    print_token(cxt->pr, "(");
    codegen_term(cxt, EXPR, MODE_VALUE, stmt->if_data.condition);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, "{");
    new_line(cxt->pr);
    end_item(cxt->pr);

    increase_indent(cxt->pr);
    codegen_statements(cxt, stmt->if_data.then_block);
    decrease_indent(cxt->pr);

    if (stmt->if_data.else_block) {
        begin_item(cxt->pr);
        print_token(cxt->pr, "}");
        print_token(cxt->pr, "else");
        print_token(cxt->pr, "{");
        new_line(cxt->pr);
        end_item(cxt->pr);

        increase_indent(cxt->pr);
        codegen_statements(cxt, stmt->if_data.else_block);
        decrease_indent(cxt->pr);
    }

    begin_item(cxt->pr);
    print_token(cxt->pr, "}");
    new_line(cxt->pr);
    end_item(cxt->pr);
}

static void codegen_while_stmt(struct CGContext *cxt,
                               struct Statement *stmt)
{
    begin_item(cxt->pr);
    print_token(cxt->pr, "while");
    print_token(cxt->pr, "(");
    print_token(cxt->pr, "1");
    print_token(cxt->pr, ")");
    print_token(cxt->pr, "{");
    new_line(cxt->pr);
    end_item(cxt->pr);

    increase_indent(cxt->pr);
    begin_item(cxt->pr);
    print_token(cxt->pr, "if");
    print_token(cxt->pr, "(");
    print_token(cxt->pr, "!");
    codegen_term(cxt, CAST_EXPR, MODE_VALUE, stmt->while_data.condition);
    print_token(cxt->pr, ")");
    print_token(cxt->pr, "break");
    print_token(cxt->pr, ";");
    new_line(cxt->pr);
    end_item(cxt->pr);
    codegen_statements(cxt, stmt->while_data.body);
    decrease_indent(cxt->pr);

    begin_item(cxt->pr);
    print_token(cxt->pr, "}");
    new_line(cxt->pr);
    end_item(cxt->pr);
}

static void codegen_statements(struct CGContext *cxt,
                               struct Statement *stmts)
{
    while (stmts) {
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
                codegen_var_decl_stmt(cxt, stmts);
                return;  // codegen_var_decl_stmt itself processes the tail stmts

            case ST_ASSIGN:
                codegen_assign_stmt(cxt, stmts);
                break;

            case ST_SWAP:
                codegen_swap_stmt(cxt, stmts);
                break;

            case ST_RETURN:
                codegen_return_stmt(cxt, stmts);
                break;

            case ST_IF:
                codegen_if_stmt(cxt, stmts);
                break;

            case ST_WHILE:
                codegen_while_stmt(cxt, stmts);
                break;

            case ST_CALL:
                codegen_call(cxt, EXPR, stmts->call.term, true);
                break;

            case ST_MATCH:
                codegen_match(cxt, stmts->match.scrutinee, stmts->match.arms, true);
                break;

            case ST_MATCH_FAILURE:
                // Do nothing. We should never reach this anyway.
                break;
            }
        }

        stmts = stmts->next;
    }
}


//
// Code generation for decls
//

static void codegen_decl_const(struct CGContext *cxt,
                               struct Decl *decl,
                               bool is_interface)
{
    char *mangled_name = mangle_name(decl->name);

    // print prototype (if exported)
    if (is_interface) {
        if (is_scalar_type(cxt, decl->const_data.type)) {
            print_token(cxt->h_pr, "extern");
            print_token(cxt->h_pr, "const");
            print_token(cxt->h_pr, scalar_type_to_name(decl->const_data.type));
            print_token(cxt->h_pr, mangled_name);
            print_token(cxt->h_pr, ";");
            new_line(cxt->h_pr);
            new_line(cxt->h_pr);
        } else {
            print_token(cxt->h_pr, "char");
            print_token(cxt->h_pr, "*");
            print_token(cxt->h_pr, mangled_name);
            print_token(cxt->h_pr, "()");
            print_token(cxt->h_pr, ";");
            new_line(cxt->h_pr);
            new_line(cxt->h_pr);
        }
    }

    if (!decl->const_data.rhs) {
        // interface decl
        free(mangled_name);
        return;
    }

    if (!decl->const_data.value) fatal_error("constant value is not known");

    // print definition
    if (is_scalar_type(cxt, decl->const_data.type)) {
        print_token(cxt->pr, "const");
        print_token(cxt->pr, scalar_type_to_name(decl->const_data.type));
        print_token(cxt->pr, mangled_name);
        print_token(cxt->pr, "=");
        codegen_term(cxt, EXPR, MODE_VALUE, decl->const_data.value);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        new_line(cxt->pr);

    } else {
        print_token(cxt->pr, "char");
        print_token(cxt->pr, "*");
        print_token(cxt->pr, mangled_name);
        print_token(cxt->pr, "()");
        new_line(cxt->pr);
        print_token(cxt->pr, "{");
        new_line(cxt->pr);

        increase_indent(cxt->pr);
        print_token(cxt->pr, "static uint8_t init = 0;");
        new_line(cxt->pr);

        char temp_name[TEMP_NAME_LEN];
        make_static_temporary(cxt, temp_name, decl->const_data.type);

        print_token(cxt->pr, "if (!init) {");
        new_line(cxt->pr);

        increase_indent(cxt->pr);
        copy_term_to_variable(cxt, temp_name, false, decl->const_data.value);

        print_token(cxt->pr, "init = 1;");
        new_line(cxt->pr);

        decrease_indent(cxt->pr);
        print_token(cxt->pr, "}");
        new_line(cxt->pr);

        print_token(cxt->pr, "return");
        print_token(cxt->pr, temp_name);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);

        decrease_indent(cxt->pr);
        print_token(cxt->pr, "}");
        new_line(cxt->pr);
        new_line(cxt->pr);

        struct CodegenEntry *entry = alloc(sizeof(struct CodegenEntry));
        memset(entry, 0, sizeof(*entry));
        entry->is_func_const = true;
        hash_table_insert(cxt->env, copy_string(decl->name), entry);
    }

    free(mangled_name);
}

// returns newly allocated string
static char* get_extern_name(struct Decl *decl)
{
    const char *dot = strrchr(decl->name, '.');
    if (dot == NULL) {
        fatal_error("unexpected: decl without '.' in name");
    }
    return copy_string(dot + 1);
}

static void print_function_header(struct CGContext *cxt,
                                  struct Decl *decl)
{
    // Start a new function
    struct Type *ret_ty = decl->function_data.return_type;
    if (ret_ty && is_scalar_type(cxt, ret_ty)) {
        codegen_type(cxt, ret_ty);
    } else {
        print_token(cxt->pr, "void");
    }

    char *mangled_name;

    if (decl->function_data.is_extern) {
        mangled_name = get_extern_name(decl);
    } else {
        mangled_name = mangle_name(decl->name);
    }
    print_token(cxt->pr, mangled_name);
    free(mangled_name);

    print_token(cxt->pr, "(");

    // Add implicit "ret" argument if return type is aggregate
    if (ret_ty && !is_scalar_type(cxt, ret_ty)) {
        print_token(cxt->pr, "char");
        print_token(cxt->pr, "*");
        print_token(cxt->pr, "ret");
        if (decl->function_data.tyvars || decl->function_data.args) {
            print_token(cxt->pr, ",");
        }
    }

    // Add implicit size argument for each type variable
    for (struct TyVarList *tv = decl->function_data.tyvars; tv; tv = tv->next) {
        print_token(cxt->pr, "uint64_t");
        mangled_name = mangle_name(tv->name);
        print_token(cxt->pr, mangled_name);
        free(mangled_name);
        if (tv->next || decl->function_data.args) {
            print_token(cxt->pr, ",");
        }
    }

    // Add the explicit arguments
    for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
        if (arg->ref) {
            print_token(cxt->pr, "char");
            print_token(cxt->pr, "*");
        } else {
            codegen_type(cxt, arg->type);
        }
        mangled_name = mangle_name(arg->name);
        print_token(cxt->pr, mangled_name);
        free(mangled_name);
        if (arg->next != NULL) print_token(cxt->pr, ",");
    }

    print_token(cxt->pr, ")");
}

static bool found_in_interface(struct Module *module,
                               const char *name)
{
    for (struct DeclGroup *group = module->interface; group; group = group->next) {
        for (struct Decl *decl = group->decl; decl; decl = decl->next) {
            if (strcmp(decl->name, name) == 0) {
                return true;
            }
        }
    }
    return false;
}

static void codegen_decl_function(struct CGContext *cxt,
                                  struct Module *module,
                                  struct Decl *decl,
                                  bool is_interface)
{
    // Write the header (only for interface decls)
    if (is_interface) {
        struct CPrinter *c_pr = cxt->pr;
        cxt->pr = cxt->h_pr;
        print_function_header(cxt, decl);
        print_token(cxt->pr, ";");
        new_line(cxt->pr);
        new_line(cxt->pr);
        cxt->pr = c_pr;
    }

    if (decl->function_data.is_extern) {
        // Extern function. Just insert a CodegenEntry and we're done.
        struct CodegenEntry *entry = alloc(sizeof(struct CodegenEntry));
        memset(entry, 0, sizeof(*entry));
        entry->foreign_name = get_extern_name(decl);
        hash_table_insert(cxt->env, copy_string(decl->name), entry);

        // We also need the prototype, if we haven't already put it in the header file
        if (!is_interface) {
            print_function_header(cxt, decl);
            print_token(cxt->pr, ";");
            new_line(cxt->pr);
            new_line(cxt->pr);
        }

        return;
    }

    // Normal function.

    if (!decl->function_data.body_specified) {
        // This must be an interface decl
        return;
    }

    // If this is not listed in the interface then we can make it "static"
    if (!found_in_interface(module, decl->name)) {
        print_token(cxt->pr, "static");
    }

    // Start the function implementation (in the C file)
    print_function_header(cxt, decl);
    new_line(cxt->pr);
    print_token(cxt->pr, "{");
    new_line(cxt->pr);

    // Add env entries for any ref arguments
    for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
        if (arg->ref) {
            struct CodegenEntry *entry = alloc(sizeof(struct CodegenEntry));
            memset(entry, 0, sizeof(*entry));
            entry->is_ref = true;
            hash_table_insert(cxt->env, arg->name, entry);
        }
    }

    // Generate code for the statements of the function
    increase_indent(cxt->pr);
    codegen_statements(cxt, decl->function_data.body);
    decrease_indent(cxt->pr);

    print_token(cxt->pr, "}");
    new_line(cxt->pr);
    new_line(cxt->pr);

    // Remove env entries for the arguments
    for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
        void *value = hash_table_lookup(cxt->env, arg->name);
        if (value) {
            free(value);
            hash_table_remove(cxt->env, arg->name);
        }
    }
}

// codegens a single Decl
static void codegen_decl(struct CGContext *cxt,
                         struct Module *module,
                         struct Decl *decl,
                         bool is_interface)
{
    if (decl->ghost) {
        return;
    }

    reset_context(cxt);

    switch (decl->tag) {
    case DECL_CONST:
        codegen_decl_const(cxt, decl, is_interface);
        break;

    case DECL_FUNCTION:
        codegen_decl_function(cxt, module, decl, is_interface);
        break;

    case DECL_DATATYPE:
        // Nothing to do
        break;

    case DECL_TYPEDEF:
        if (decl->typedef_data.rhs == NULL) {
            // We need to record that this is an "abstract" type (and therefore
            // its size cannot be calculated).
            struct CodegenEntry *entry = alloc(sizeof(struct CodegenEntry));
            memset(entry, 0, sizeof(*entry));
            entry->is_abstract_type = true;
            hash_table_insert(cxt->env, copy_string(decl->name), entry);
        }
        break;
    }
}

static void codegen_root(FILE *file,
                         struct Module *module,
                         bool generate_main)
{
    // C main function
    if (generate_main) {
        fprintf(file, "int main()\n");
        fprintf(file, "{\n");
        char *main_name = copy_string_2(module->name, ".main");
        char *mangled_name = mangle_name(main_name);
        free(main_name);
        fprintf(file, "    %s();\n", mangled_name);
        free(mangled_name);
        fprintf(file, "}\n");
    }
}

struct HashTable * new_codegen_env()
{
    return new_hash_table();
}

static void free_codegen_entry(void *context, const char *key, void *value)
{
    struct CodegenEntry *entry = value;
    free((void*)entry->foreign_name);
    free((void*)key);
    free(value);
}

void free_codegen_env(struct HashTable *env)
{
    hash_table_for_each(env, free_codegen_entry, NULL);
    free_hash_table(env);
}

static void print_includes(FILE *file, struct Import *imports)
{
    while (imports) {
        if (strcmp(imports->module_name, "Int") != 0) {
            fprintf(file, "#include \"%s.h\"\n", imports->module_name);
        }
        imports = imports->next;
    }
}

void codegen_module(FILE *c_output_file,
                    FILE *h_output_file,
                    struct HashTable *codegen_env,
                    struct Module *module,
                    bool root,
                    bool generate_main)
{
    const char *banner = "/* This file was generated automatically by the Babylon compiler. */\n\n";

    fprintf(h_output_file, "%s", banner);
    char *mangled_module_name = mangle_name(module->name);
    fprintf(h_output_file, "#ifndef BAB_MODULE_%s\n", mangled_module_name);
    fprintf(h_output_file, "#define BAB_MODULE_%s\n\n", mangled_module_name);
    fprintf(h_output_file, "#include <stdint.h>\n\n");

    print_includes(h_output_file, module->interface_imports);
    fprintf(h_output_file, "\n");

    fprintf(c_output_file, "%s", banner);
    fprintf(c_output_file, "#include <stdint.h>\n");
    fprintf(c_output_file, "#include <string.h>\n\n");

    fprintf(c_output_file, "#include \"%s.h\"\n", module->name);
    print_includes(c_output_file, module->implementation_imports);
    fprintf(c_output_file, "\n");

    struct CGContext cxt;
    cxt.env = codegen_env;
    cxt.pr = new_c_printer(c_output_file);
    cxt.h_pr = new_c_printer(h_output_file);
    cxt.tmp_num = 0;

    for (struct DeclGroup *decls = module->interface; decls; decls = decls->next) {
        for (struct Decl *decl = decls->decl; decl; decl = decl->next) {
            codegen_decl(&cxt, module, decl, true);
        }
    }

    for (struct DeclGroup *decls = module->implementation; decls; decls = decls->next) {
        for (struct Decl *decl = decls->decl; decl; decl = decl->next) {
            codegen_decl(&cxt, module, decl, false);
        }
    }

    if (root) {
        codegen_root(c_output_file, module, generate_main);
    }

    fprintf(h_output_file, "#endif  /* BAB_MODULE_%s */\n", mangled_module_name);

    free(mangled_module_name);
    free_c_printer(cxt.pr);
    free_c_printer(cxt.h_pr);
}
