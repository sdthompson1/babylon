/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_FUNC_H
#define VERIFIER_FUNC_H

// Some helpers for verifying functions and calls


// Return the "expanded" return type for a function.
// If there are ref args the expanded return type is a tuple of ret_type
//   (or {} if the function is void) followed by the types of the ref args.
// Otherwise the return type is a copy of the ret_type (or {} if the
//   function is void).
struct Type *get_expanded_ret_type(struct FunArg *args, struct Type *ret_ty);


// Given an expanded return type (converted to FOL) returns the corresponding
// $FLDn constructor. (Requires that there was at least one ref argument.)
struct Sexpr *ret_fldn(int n, struct Sexpr *fol_ret_ty);

// Returns an expression indicating that "%return" is valid.
// Checks both the return-value, and any updated ref-args.
struct Sexpr *ret_validity_test(struct FunArg *args, struct Type *ret_ty, struct Sexpr *fol_ret_ty);

// Turn EXPR into (let ((%return RET_DEFN)) EXPR) but only if EXPR contains %return.
// Hands over both arguments.
struct Sexpr * add_return_if_required(struct Sexpr *ret_defn, struct Sexpr *expr);


// Insert any lets required for locally-defined variables. (Can return NULL.)
// expr is handed over.
struct Sexpr * insert_lets(struct VContext *context, struct Sexpr *expr);


// Verify a return statement, or the implicit return at the end of a void function
//  - Verifies the given return-value (if any) is valid
//  - Verifies postconditions are true
//  - If ghost==false, verifies that return value(s) are not allocated.
//  - Inserts a definitional axiom for the current function if possible.
// Returns true if successful.
bool verify_function_return(struct VContext *context,
                            struct Location location,
                            struct Term *return_value,
                            bool ghost,
                            struct Sexpr *** ret_val_ptr);

#endif
