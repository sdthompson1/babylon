/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef FOL_H
#define FOL_H

/* A FOL problem is stored in an S-expr notation, similar to SMT-LIB but with some customisations.


Top-level items:

  (declare-sort sortname 0)
  (declare-const constname ty)
  (declare-fun funname (ty1 ty2..) retty)
  (define-fun funname ((x1 ty1)..) retty term)
  (assert term)
  (prove term)

  (generic name (variables) command)


Instances of generics:

  (instance name (values))


Types:

  Bool
  Int
  sortname                                type declared using declare-sort
  (instance $PROD (ty0 .. tyn))           product type
  $PROD                                   empty product type (a.k.a. "unit")
                                           (this is actually part of initial_env.c, not built-in)
  (instance $SUM (ty0 .. tyn))            sum type
  (Array index-type element-type)         SMT-LIB arrays


Terms:

  123                integer constants
  -456
  true               boolean constants
  false

  var                variable or constant reference
  (name arg arg)     application

  (and arg..)        and
  (or arg..)         or
  (xor arg..)        xor
  (not arg)          not
  (=> arg1 arg2)     implication

  (ite term1 term2 term3)                          if-then-else
  (match ...)                                      match expression (see SMT-LIB spec)

  (let ((v1 term1) (v2 term2) ..) term)            let
  (forall ((v1 ty1) (v2 ty2) ..) term)             quantifiers
  (exists ((v1 ty1) (v2 ty2) ..) term)

  (= arg1 arg2)      equality
  (distinct arg..)   distinctness (not-equals)
  (< x y)
  (<= x y)
  (> x y)
  (>= x y)

  (+ arg..)      arithmetic operators
  (- x)
  (- x y)
  (* x y)
  (div x y)    Note uses SMT-LIB convention i.e. if y>0 then floor(x/y) else ceil(x/y)
  (mod x y)

  ((instance $PROD (Int Int)) 10 20)            product construction
  $PROD                                         empty product construction
  ((instance $FLD0 (Int Int)) product_term)     product field projection

  ((instance $IN1 (Int Bool)) true)             variant construction
  ((instance $INF1 (Int Bool)) variant-term)    variant projection
  ((_ is $IN1) variant-term)                    variant testing
  (match variant_term                           variant matching
      (((instance $IN0 (Int Bool)) i) (+ i 1))
      (((instance $IN1 (Int Bool)) b) (not b)))

  (select array index)                          array operations
  (store array index element)


Also ($lambda (args) expr) can be used in generics, this will be
substituted out by substitute_in_sexpr.


Variable name conventions:

In order to avoid clashes with SMT-LIB reserved names, the verifier
prefixes all names that it defines with either "%" or "$".

 - "%" indicates a name from the program, e.g. "%x" or "%Main.main".

 - "$" indicates an internal helper of some sort, e.g. "$can_mul_i32".

The renamer might have already added some other characters e.g.

 - "^" indicates a type, e.g. "%^a" (a type variable) or
   "%Main.^Color" (a datatype Color defined in module Main).

 - "@" indicates different source-code level names for a variable,
      e.g. if a function has two local variables "x" in different
      scopes, they might be end up with names "%x" and "%x@1".

The verifier also uses certain other conventions e.g.

 - "." plus a number indicates a different version of a variable. E.g.
   a local variable might be called "%x" when it is first defined, but
   "%x.1" after its first assignment. (This can also be combined with
   "@" e.g. "%x@2.3" might be version 3 of variable x in scope 2.)

 - Datatype field names include the constructor name, e.g.
   "%Main.^MyType-myfield" for a field myfield of a datatype MyType
   defined in the Main module.

In addition convert_fol_to_smt assumes that names do not contain the
"-" or "!" characters.

*/

struct Sexpr;


enum FolResult {
    FOL_RESULT_PROVED,
    FOL_RESULT_DISPROVED,
    FOL_RESULT_UNKNOWN
};

// this frees "problem" (and all children) after solving
enum FolResult solve_fol_problem(struct Sexpr *problem,
                                 const char *cache_prefix,
                                 const char *debug_filename,
                                 bool print_progress_messages,
                                 int timeout_seconds);


#endif
