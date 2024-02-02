/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef SIZE_EXPR_H
#define SIZE_EXPR_H

#include <stdbool.h>
#include <stdint.h>

// A struct representing a runtime-known size, as a function of
// some unknown size-variables.
struct SizeExpr;


// Free a SizeExpr
void free_size_expr(struct SizeExpr *);

// Copy a SizeExpr
struct SizeExpr * copy_size_expr(struct SizeExpr *);


// Return a new SizeExpr representing "zero"
// (This may be represented as a NULL pointer)
struct SizeExpr * zero_size_expr();

// Return a new SizeExpr representing a given constant
struct SizeExpr * const_size_expr(uint64_t value);

// Return a new SizeExpr representing "multiplier" times the given variable name.
// (varname is copied, and should be the "mangled" name.)
// Multiplier should be >= 0, and it is assumed that the variable will always
// be >= 0 as well.
struct SizeExpr * var_size_expr(const char *varname, uint64_t multiplier);


// Return a new SizeExpr representing the sum of two other sizes.
struct SizeExpr * add_size_expr(struct SizeExpr *lhs, struct SizeExpr *rhs);

// Return a new SizeExpr representing a constant multiplied by another size.
struct SizeExpr * multiply_size_expr(uint64_t lhs, struct SizeExpr *rhs);

// Return a new SizeExpr representing the max of two other sizes.
struct SizeExpr * max_size_expr(struct SizeExpr *lhs, struct SizeExpr *rhs);


// True if the SizeExpr is a compile-time known constant.
bool is_size_expr_const(struct SizeExpr *);

// True if the SizeExpr is zero.
bool is_size_expr_zero(struct SizeExpr *);

// Returns the value of the size_expr. Only valid if is_size_expr_const returns true.
uint64_t get_size_expr_const(struct SizeExpr *);


// Print a size expr to a C printer.
// Produces a C "additive expression" (and possibly some variable declarations).
// The function "make_temp_name" creates a new temporary variable name, which
// is then freed by print_size_expr.
struct CPrinter;
void write_size_expr(struct CPrinter *printer,
                     struct SizeExpr *expr,
                     char * (*new_temp_name)(void *temp_name_context),
                     void *temp_name_context);

#endif
