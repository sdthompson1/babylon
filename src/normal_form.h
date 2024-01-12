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
//  - TM_RECORD with normal-form sub-terms
//  - TM_VARIANT with normal-form payload


// Given an int literal string, return the value as uint64_t
// (to interpret as signed, memcpy the result to int64_t)
uint64_t parse_int_literal(const char *data);

// Convert a TM_DEFAULT (int or bool type), TM_INT_LITERAL, or TM_BOOL_LITERAL to uint64_t
uint64_t normal_form_to_int(const struct Term *term);

// Make a normal form term from a type and value.
// The type must be TY_FINITE_INT or TY_BOOL.
struct Term * make_literal_of_type(struct Type *type, uint64_t value);

#endif

