/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef AST_H
#define AST_H

#include "location.h"
#include "sha256.h"

#include <stdbool.h>
#include <stdint.h>


//
// Types
//

enum TypeTag {
    TY_VAR,        // variable (or type-name)
    TY_BOOL,
    TY_FINITE_INT,
    TY_MATH_INT,
    TY_MATH_REAL,
    TY_RECORD,
    TY_VARIANT,
    TY_ARRAY,
    TY_FUNCTION,
    TY_FORALL,
    TY_LAMBDA,
    TY_APP
};

struct Type;


struct TypeList {
    struct Type *type;
    struct TypeList *next;
};

struct TyVarList {
    const char *name;
    struct TyVarList *next;
};

struct NameTypeList {
    const char *name;
    struct Type *type;
    struct NameTypeList *next;
};


struct TypeData_Int {
    bool is_signed;
    int num_bits;
};

struct TypeData_Record {
    // for tuples, 'name' will be NULL before typechecking, but will
    // be set to a numeric name ("0", "1" etc) after typechecking.
    struct NameTypeList *fields;
};

struct TypeData_Variant {
    struct NameTypeList *variants;    // the types can be NULL, until after typechecking
};

struct TypeData_Array {
    struct Type *element_type;
    int ndim;
};

struct TypeData_Function {
    struct FunArg * args;           // names are NULL
    struct Type * return_type;      // may be NULL
};

struct TypeData_Forall {
    struct TyVarList *tyvars;
    struct Type *type;
};

struct TypeData_Lambda {
    struct TyVarList *tyvars;
    struct Type *type;
};

struct TypeData_Var {
    const char *name;
};

struct TypeData_App {
    struct Type *lhs;
    struct TypeList *tyargs;
};

struct Type {
    struct Location location;
    enum TypeTag tag;
    union {
        struct TypeData_Var var_data;
        struct TypeData_Int int_data;
        struct TypeData_Record record_data;
        struct TypeData_Variant variant_data;
        struct TypeData_Array array_data;
        struct TypeData_Function function_data;
        struct TypeData_Forall forall_data;
        struct TypeData_Lambda lambda_data;
        struct TypeData_App app_data;
    };
};


//
// Patterns and Arms
//

enum PatternTag {
    // Pre-typechecking - match can be used for anything
    PAT_VAR,
    PAT_BOOL,
    PAT_INT,
    PAT_RECORD,

    // Post-typechecking - only variant and wildcard patterns allowed.
    // Also, PAT_VARIANT will not repeat cases, all payloads will be
    // PAT_VAR with ref=true or PAT_WILDCARD, and all matches will be
    // exhaustive (although they might lead to "MATCH_FAILURE").
    PAT_VARIANT,
    PAT_WILDCARD
};

struct PatData_Var {
    const char *name;
    bool ref;
};

struct PatData_Bool {
    bool value;
};

struct PatData_Int {
    const char *data;  // contains only digits 0-9 and possibly a single initial '-'.
    // No leading 0's unless the number is zero in which case there is a single 0.
};

struct PatData_Record {
    struct NamePatternList *fields;
};

struct PatData_Variant {
    const char *variant_name;
    struct Pattern *payload;     // can be NULL, until after typechecking
};

struct Pattern {
    struct Location location;
    enum PatternTag tag;
    union {
        struct PatData_Var var;
        struct PatData_Bool bool_data;
        struct PatData_Int int_data;
        struct PatData_Record record;
        struct PatData_Variant variant;
    };
};

struct NamePatternList {
    const char *name;           // can be NULL
    struct Pattern *pattern;
    struct NamePatternList *next;
};

struct Arm {
    struct Location location;
    struct Pattern *pattern;
    void *rhs;   // Points to either Term or Statement as appropriate
    struct Arm *next;
};



//
// Terms
//

enum TermTag {
    TM_VAR,
    TM_DEFAULT,
    TM_BOOL_LITERAL,
    TM_INT_LITERAL,
    TM_STRING_LITERAL,
    TM_CAST,
    TM_IF,
    TM_UNOP,
    TM_BINOP,
    TM_LET,
    TM_QUANTIFIER,
    TM_CALL,
    TM_TYAPP,
    TM_RECORD,
    TM_RECORD_UPDATE,
    TM_FIELD_PROJ,
    TM_VARIANT,
    TM_MATCH,
    TM_MATCH_FAILURE,
    TM_SIZEOF,
    TM_ALLOCATED,
    TM_ARRAY_PROJ
};

struct TermData_Var {
    const char *name;     // variable name. After renaming, will be qualified if applicable.
    bool postcond_new;    // this will be false outside of a postcondition
};

struct TermData_BoolLiteral {
    bool value;
};

struct TermData_IntLiteral {
    const char *data;  // contains only digits 0-9 and possibly a single initial '-'
};

struct TermData_StringLiteral {
    const uint8_t *data;  // *Not* NUL-terminated. May contain NUL characters.
    uint32_t length;
};

struct TermData_Cast {
    struct Type *target_type;
    struct Term *operand;
};

struct TermData_If {
    struct Term *cond;
    struct Term *then_branch;
    struct Term *else_branch;
};


enum UnOp {
    UNOP_NEGATE,
    UNOP_COMPLEMENT,
    UNOP_NOT
};

enum BinOp {
    BINOP_PLUS,
    BINOP_MINUS,
    BINOP_TIMES,
    BINOP_DIVIDE,
    BINOP_MODULO,

    BINOP_BITAND,
    BINOP_BITOR,
    BINOP_BITXOR,
    BINOP_SHIFTLEFT,
    BINOP_SHIFTRIGHT,

    BINOP_EQUAL,
    BINOP_NOT_EQUAL,
    BINOP_LESS,
    BINOP_LESS_EQUAL,
    BINOP_GREATER,
    BINOP_GREATER_EQUAL,

    BINOP_AND,
    BINOP_OR,
    BINOP_IMPLIES,
    BINOP_IMPLIED_BY,   // Converted to BINOP_IMPLIES by typechecker
    BINOP_IFF
};

struct TermData_UnOp {
    enum UnOp operator;
    struct Term *operand;
};

// This allows for chaining e.g. a < b <= c or a == b == c.
// Note chaining is removed by the typechecker.
// We also re-use this same struct for function calls, but the operators
// are ignored in that case.
struct OpTermList {
    enum BinOp operator;
    struct Term *rhs;
    struct OpTermList *next;
};

struct TermData_BinOp {
    struct Term *lhs;
    struct OpTermList *list;
};

struct TermData_Let {
    const char *name;   // New variable name
    // TODO: could maybe allow a type annotation here.
    // TODO: maybe could allow multiple lets simultaneously?
    struct Term *rhs;   // New variable value
    struct Term *body;  // Term that uses the new variable
};

enum Quantifier {
    QUANT_FORALL,
    QUANT_EXISTS
};

struct TermData_Quantifier {
    enum Quantifier quant;
    const char *name;
    struct Type *type;
    struct Term *body;
};

struct TermData_Call {
    struct Term *func;
    struct OpTermList *args;
};

struct TermData_TyApp {
    struct Term *lhs;
    struct TypeList *tyargs;
};

struct NameTermList {
    struct Location location;
    const char *name;
    struct Term *term;
    struct NameTermList *next;
};

struct TermData_Record {
    struct NameTermList *fields;
};

struct TermData_RecordUpdate {
    struct Term *lhs;
    struct NameTermList *fields;
};

struct TermData_FieldProj {
    struct Term *lhs;
    const char *field_name;
};

struct TermData_Variant {
    const char *variant_name;
    struct Term *payload;
};

struct TermData_Match {
    struct Term *scrutinee;
    struct Arm *arms;
};

struct TermData_Sizeof {
    struct Term *rhs;
};

struct TermData_Allocated {
    struct Term *rhs;
};

struct TermData_ArrayProj {
    struct Term *lhs;
    struct OpTermList *indexes;
};

struct Term {
    struct Location location;
    struct Type *type;   // this is NULL after parsing but filled by typechecker
    enum TermTag tag;
    union {
        struct TermData_Var var;
        struct TermData_BoolLiteral bool_literal;
        struct TermData_IntLiteral int_literal;
        struct TermData_StringLiteral string_literal;
        struct TermData_Cast cast;
        struct TermData_If if_data;
        struct TermData_UnOp unop;
        struct TermData_BinOp binop;
        struct TermData_Let let;
        struct TermData_Quantifier quant;
        struct TermData_Call call;
        struct TermData_TyApp tyapp;
        struct TermData_Record record;
        struct TermData_RecordUpdate record_update;
        struct TermData_FieldProj field_proj;
        struct TermData_Variant variant;
        struct TermData_Match match;
        struct TermData_Sizeof sizeof_data;
        struct TermData_Allocated allocated;
        struct TermData_ArrayProj array_proj;
    };
    int sethi_ullman_number;  // only used by code generator
};



//
// Attributes
//

// An attribute is something that a declaration (or statement) can
// have, such as a precondition or postcondition.

enum AttrTag {
    ATTR_REQUIRES,
    ATTR_ENSURES,
    ATTR_INVARIANT,
    ATTR_DECREASES
};

struct Attribute {
    struct Location location;
    enum AttrTag tag;
    union {
        struct Term *term;
    };
    struct Attribute *next;

    bool valid;  // used during verification only
};



//
// Statements
//

enum StmtTag {
    ST_VAR_DECL,
    ST_FIX,
    ST_OBTAIN,
    ST_USE,
    ST_ASSIGN,
    ST_SWAP,
    ST_RETURN,
    ST_ASSERT,
    ST_ASSUME,
    ST_IF,
    ST_WHILE,
    ST_CALL,
    ST_MATCH,
    ST_MATCH_FAILURE,
    ST_SHOW_HIDE
};

struct StmtData_VarDecl {
    const char *name;
    struct Type *type;  // may be NULL pre-typechecking; non-NULL after.
    struct Term *rhs;   // ditto
    bool ref;
};

struct StmtData_Fix {
    const char *name;
    struct Type *type;
};

struct StmtData_Obtain {
    const char *name;
    struct Type *type;
    struct Term *condition;
};

struct StmtData_Use {
    struct Term *term;
};

struct StmtData_Assign {
    struct Term *lhs;
    struct Term *rhs;
};

struct StmtData_Swap {
    struct Term *lhs;
    struct Term *rhs;
};

struct StmtData_Return {
    struct Term *value;   // may be NULL
};

struct StmtData_Assert {
    struct Term *condition;
    struct Statement *proof;  // may be NULL
};

struct StmtData_Assume {
    struct Term *condition;
};

struct StmtData_If {
    struct Term *condition;
    struct Statement *then_block;   // may be NULL
    struct Statement *else_block;   // may be NULL
};

struct StmtData_While {
    struct Term *condition;
    struct Attribute *attributes;
    struct Statement *body;
};

struct StmtData_Call {
    struct Term *term;   // Always TM_CALL (ensured by parser). Type is NULL even after typechecking.
};

struct StmtData_Match {
    struct Term *scrutinee;
    struct Arm *arms;
};

struct StmtData_ShowHide {
    const char *name;
    bool show;
};

struct Statement {
    struct Location location;
    struct Statement *next;
    enum StmtTag tag;
    union {
        struct StmtData_VarDecl var_decl;
        struct StmtData_Fix fix;
        struct StmtData_Obtain obtain;
        struct StmtData_Use use;
        struct StmtData_Assign assign;
        struct StmtData_Swap swap;
        struct StmtData_Return ret;
        struct StmtData_Assert assert_data;
        struct StmtData_Assume assume;
        struct StmtData_If if_data;
        struct StmtData_While while_data;
        struct StmtData_Call call;
        struct StmtData_Match match;
        struct StmtData_ShowHide show_hide;
    };
    bool ghost;
};



//
// Declarations
//

enum DeclTag {
    DECL_CONST,
    DECL_FUNCTION,
    DECL_DATATYPE,
    DECL_TYPEDEF
};


struct FunArg {
    const char *name;
    struct Type *type;

    // True if this is a "ref" argument; set by parser.
    bool ref;

    struct FunArg *next;
};

struct DataCtor {
    struct Location location;
    const char *name;
    struct Type *payload;   // can be NULL
    struct DataCtor *next;
};


struct DeclData_Const {
    struct Type *type;  // non-NULL (after typechecking)
    struct Term *rhs;   // non-NULL for implementations (after typechecking)
    struct Term *value; // Normal form of rhs (non-ghost only)
};

struct DeclData_Function {
    struct TyVarList *tyvars;
    struct FunArg *args;
    struct Type *return_type;  // can be NULL

    struct Statement *body;    // can be NULL if body is empty
    bool body_specified;       // true if 'begin' and 'end' given (even if empty)

    struct Location end_loc;

    bool is_extern;
};

struct DeclData_Datatype {
    struct TyVarList *tyvars;
    struct DataCtor *ctors;
};

struct DeclData_Typedef {
    struct TyVarList *tyvars;
    struct Type *rhs;
    bool allocated;  // applicable to 'abstract' typedefs (rhs=NULL)
};

struct Decl {
    struct Location location;
    const char *name;

    enum DeclTag tag;
    union {
        struct DeclData_Const const_data;
        struct DeclData_Function function_data;
        struct DeclData_Datatype datatype_data;
        struct DeclData_Typedef typedef_data;
    };

    struct Attribute *attributes;

    struct Decl *next;   // next decl in same group

    bool recursive;      // filled in by dependency resolver
    bool ghost;
};



//
// Modules
//

struct Import {
    struct Location location;
    const char * module_name;
    const char * alias_name;  // not NULL
    bool qualified;
    struct Import *next;
};

struct DeclGroup {
    struct Decl *decl;
    struct DeclGroup *next;
};

struct Module {
    const char *name;
    struct DeclGroup *interface;
    struct DeclGroup *implementation;
    struct Import *interface_imports;   // cleared by renamer (as no longer needed after that)
    struct Import *implementation_imports;  // ditto

    uint8_t interface_checksum[SHA256_HASH_LENGTH];
    uint8_t implementation_checksum[SHA256_HASH_LENGTH];
};



//
// Recursive "Transform" functions
//

struct TypeTransform {
    void * (*transform_var) (void *context, struct Type *type_var);
    void * (*transform_bool) (void *context, struct Type *type_bool);
    void * (*transform_finite_int) (void *context, struct Type *type_finite_int);
    void * (*transform_math_int) (void *context, struct Type *type_math_int);
    void * (*transform_math_real) (void *context, struct Type *type_math_real);
    void * (*transform_record) (void *context, struct Type *type_record, void *fields_result);
    void * (*transform_variant) (void *context, struct Type *type_variant, void *variants_result);
    void * (*transform_array) (void *context, struct Type *type_array, void *elt_type_result);
    void * (*transform_function) (void *context, struct Type *type_function, void *args_result, void *return_type_result);
    void * (*transform_forall) (void *context, struct Type *type_forall, void *tyvars_result, void *child_type_result);
    void * (*transform_lambda) (void *context, struct Type *type_lambda, void *tyvars_result, void *type_result);
    void * (*transform_app) (void *context, struct Type *type_app, void *lhs_result, void *tyargs_result);


    // these are called for each individual node in any
    // lists encountered
    void * (*transform_tyvar_list) (void *context, struct TyVarList *node, void *next_result);
    void * (*transform_type_list) (void *context, struct TypeList *node, void *type_result, void *next_result);
    void * (*transform_name_type_list) (void *context, struct NameTypeList *node, void *type_result, void *next_result);
    void * (*transform_fun_arg) (void *context, struct FunArg *node, void *type_result, void *next_result);
};


struct TermTransform {
    void * (*transform_var) (void *context, struct Term *term_var, void *type_result);
    void * (*transform_default) (void *context, struct Term *term_default, void *type_result);
    void * (*transform_bool_literal) (void *context, struct Term *term_bool_literal, void *type_result);
    void * (*transform_int_literal) (void *context, struct Term *term_int_literal, void *type_result);
    void * (*transform_string_literal) (void *context, struct Term *term_string_literal, void *type_result);
    void * (*transform_cast) (void *context, struct Term *term_cast, void *type_result, void *target_type_result, void *operand_result);
    void * (*transform_if) (void *context, struct Term *term_if, void *type_result, void *cond_result, void *then_result, void *else_result);
    void * (*transform_unop) (void *context, struct Term *term_unop, void *type_result, void *operand_result);
    void * (*transform_binop) (void *context, struct Term *term_binop, void *type_result, void *lhs_result, void *list_result);
    void * (*transform_let) (void *context, struct Term *term_let, void *type_result, void *rhs_result, void *body_result);
    void * (*transform_quantifier) (void *context, struct Term *term_quantifier, void *type_result, void *var_type_result, void *body_result);
    void * (*transform_call) (void *context, struct Term *term_call, void *type_result, void *func_result, void *args_result);
    void * (*transform_tyapp) (void *context, struct Term *term_tyapp, void *type_result, void *lhs_result, void *tyargs_result);
    void * (*transform_record) (void *context, struct Term *term_record, void *type_result, void *fields_result);
    void * (*transform_record_update) (void *context, struct Term *term_record_update, void *type_result, void *lhs_result, void *fields_result);
    void * (*transform_field_proj) (void *context, struct Term *term_field_proj, void *type_result, void *lhs_result);
    void * (*transform_variant) (void *context, struct Term *term_variant, void *type_result, void *payload_result);
    void * (*transform_match) (void *context, struct Term *term_match, void *type_result, void *scrut_result, void *arm_result);
    void * (*transform_match_failure) (void *context, struct Term *term_match_failure, void *type_result);
    void * (*transform_sizeof) (void *context, struct Term *term_sizeof, void *type_result, void *rhs_result);
    void * (*transform_allocated) (void *context, struct Term *term_allocated, void *type_result, void *rhs_result);
    void * (*transform_array_proj) (void *context, struct Term *term_array_proj, void *type_result, void *lhs_result, void *index_results);

    // Non-recursive versions of the above.
    // If any of these are non-NULL, they will be called instead of the normal
    // function, and the transform will not descend to sub-terms automatically.
    // However, the TermTransform is passed in order to facilitate manual
    // recursion, if desired.
    void * (*nr_transform_if) (struct TermTransform *tr, void *context, struct Term *term_if, void *type_result);
    void * (*nr_transform_binop) (struct TermTransform *tr, void *context, struct Term *term_binop, void *type_result);
    void * (*nr_transform_let) (struct TermTransform *tr, void *context, struct Term *term_let, void *type_result);
    void * (*nr_transform_quantifier) (struct TermTransform *tr, void *context, struct Term *term_quant, void *type_result);
    void * (*nr_transform_call) (struct TermTransform *tr, void *context, struct Term *term_call, void *type_result);
    void * (*nr_transform_tyapp) (struct TermTransform *tr, void *context, struct Term *term_tyapp, void *type_result);
    void * (*nr_transform_field_proj) (struct TermTransform *tr, void *context, struct Term *term_field_proj, void *type_result);
    void * (*nr_transform_match) (struct TermTransform *tr, void *context, struct Term *term_match, void *type_result);
    void * (*nr_transform_array_proj) (struct TermTransform *tr, void *context, struct Term *term_array_proj, void *type_result);

    // The below are called for each individual node of any lists encountered.
    void * (*transform_op_term_list) (void *context, struct OpTermList *op_term_list, void *rhs_result, void *next_result);
    void * (*transform_name_term_list) (void *context, struct NameTermList *name_term_list, void *term_result, void *next_result);
    void * (*transform_arm) (void *context, struct Arm *arm, void *rhs_result, void *next_result);

    // We deal with types by delegating to a separate TypeTransform.
    struct TypeTransform type_transform;
};

void * transform_type_list(struct TypeTransform *transform, void *context, struct TypeList *list);
void * transform_tyvar_list(struct TypeTransform *transform, void *context, struct TyVarList *list);
void * transform_name_type_list(struct TypeTransform *transform, void *context, struct NameTypeList *list);
void * transform_fun_args(struct TypeTransform *transform, void *context, struct FunArg *args);
void * transform_type(struct TypeTransform *transform, void *context, struct Type *type);

void * transform_op_term_list(struct TermTransform *transform, void *context, struct OpTermList *list);
void * transform_name_term_list(struct TermTransform *transform, void *context, struct NameTermList *list);
void * transform_arm(struct TermTransform *transform, void *context, struct Arm *arm);
void * transform_term(struct TermTransform *transform, void *context, struct Term *term);




//
// Constructors/Destructors -- Types
//

struct Type * make_type(struct Location loc, enum TypeTag tag);
struct Type * make_int_type(struct Location loc, bool is_signed, int num_bits);

void copying_type_transform(struct TypeTransform *tr);
struct Type * copy_type(const struct Type *type);
struct TypeList * copy_type_list(const struct TypeList *type_list);
struct TyVarList * copy_tyvar_list(const struct TyVarList *tyvars);

void free_type(struct Type *type);
void free_tyvar_list(struct TyVarList *tyvars);
void free_type_list(struct TypeList *types);
void free_name_type_list(struct NameTypeList *types);


//
// Constructors/Destructors -- Patterns
//

struct Pattern * make_pattern(struct Location loc, enum PatternTag tag);
struct Pattern * copy_pattern(const struct Pattern *pattern);
void free_name_pattern_list(struct NamePatternList *list);
void free_pattern(struct Pattern *pattern);


//
// Constructors/Destructors -- Terms
//

// Note: the following will copy any char* arguments.
struct Term * make_term(struct Location loc, enum TermTag tag);
struct Term * make_bool_literal_term(struct Location loc, bool value);
struct Term * make_int_literal_term(struct Location loc, const char *data);
struct Term * make_string_literal_term(struct Location loc, const uint8_t *data, uint32_t length);
struct Term * make_var_term(struct Location loc, const char *name);

struct Term * copy_term(const struct Term *term);

void free_term(struct Term *term);
void free_name_term_list(struct NameTermList *list);


//
// Constructors/Destructors -- Other
//

struct Statement * make_statement(struct Location loc, enum StmtTag tag);

struct Statement * copy_statement(struct Statement *);
struct Attribute * copy_attributes(struct Attribute *);

void free_statement(struct Statement *stmt);
void free_fun_arg(struct FunArg *);
void free_attributes(struct Attribute *attr);
void free_decl(struct Decl *);
void free_import(struct Import *);
void free_decl_group(struct DeclGroup *);
void free_module(struct Module *);


//
// Other helper functions
//

int tyvar_list_length(const struct TyVarList *list);
int type_list_length(const struct TypeList *list);

// Checks for syntactic equality of types
bool type_lists_equal(const struct TypeList *lhs, const struct TypeList *rhs);
bool types_equal(const struct Type *lhs, const struct Type *rhs);

#endif
