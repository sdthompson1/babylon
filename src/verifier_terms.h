/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef VERIFIER_TERMS_H
#define VERIFIER_TERMS_H

struct Sexpr;
struct Term;
struct VContext;

struct Sexpr * add_funarg_lets(struct Item *item, struct Sexpr *cond,
                               struct Sexpr *generic_arg_list, struct Sexpr *arglist);

// Returns a converted Sexpr, or NULL if verification fails.
struct Sexpr * verify_term(struct VContext *context, struct Term *term);

struct Sexpr * verify_call_term(struct VContext *cxt,
                                struct Term *term);

bool bind_payload(struct VContext *context,
                  struct Term *scrutinee,
                  struct PatData_Variant *pat_data);

struct RefChain *ref_chain_for_term(struct VContext *context, struct Term *term);

bool validate_ref_chain(struct VContext *context, struct RefChain *ref, struct Location location);
struct Sexpr *ref_chain_to_sexpr(struct VContext *context, struct RefChain *ref);
void update_reference(struct VContext *context, struct RefChain *ref, struct Sexpr *expr);

#endif
