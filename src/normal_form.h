/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef NORMAL_FORM_H
#define NORMAL_FORM_H

// Functions for working with normal-forms of terms.

// The normal forms are:
//  - TM_DEFAULT
//  - TM_BOOL_LITERAL
//  - TM_INT_LITERAL
//  - TM_STRING_LITERAL
//  - TM_ARRAY_LITERAL with normal-form sub-terms
//  - TM_CAST applied to TM_STRING_LITERAL or TM_ARRAY_LITERAL (casting T[n] to T[])
//  - TM_RECORD with normal-form sub-terms
//  - TM_VARIANT with normal-form payload


// Convert a TM_DEFAULT (int or bool type), TM_INT_LITERAL, or TM_BOOL_LITERAL to uint64_t
// (If the value is negative, it will be returned in twos complement form)
uint64_t normal_form_to_int(const struct Term *term);

// Determine if a given value (sign extended to 64 bits, and cast to uint64_t)
// is in range for the given type (must be TY_FINITE_INT or TY_BOOL).
bool is_value_in_range_for_type(struct Type *type, uint64_t value);

// Make a normal form term from a type and value.
// The type must be TY_FINITE_INT or TY_BOOL.
// The value must be in range for the type.
struct Term * make_literal_of_type(struct Type *type, uint64_t value);

#endif
