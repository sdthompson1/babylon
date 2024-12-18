/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef FOL_H
#define FOL_H

/* A FOL problem is stored in an S-expr notation, similar to SMT-LIB but with some customisations.


Top-level items:

  (declare-sort sortname 0)
  (declare-datatypes ((name 0)) ...)
  (declare-const constname ty)
     ; note: define-const doesn't work in vampire - use define-fun (with no args) instead.
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
"-", "~" or "!" characters.

*/

#include "cache_db.h"

struct ProverConfig;
struct Sexpr;


// FOL problems are run asynchronously by a "FolRunner".
// The CacheDb (if provided) should be kept alive at least until stop_fol_runner is called.
void start_fol_runner(struct CacheDb *cache_db,
                      struct ProverConfig *provers,
                      const char *config_filename,  // for error messages
                      int max_child_processes,
                      bool continue_after_error);

void stop_fol_runner();

// this returns the continue_after_error flag that was passed to start_fol_runner
bool fol_continue_after_error();


// Start a new FOL problem solution in the background.
// (May block if job queue is too full.)
void solve_fol_problem(struct Sexpr *problem,          // handover
                       bool show_progress,
                       const char *announce_msg,       // handover
                       const char *error_msg,          // handover
                       const char *debug_filename);


// Schedule a message to be printed when a particular point in the
// output stream is reached.
// If 'hash' is not NULL, arrange for the given hash to be added
// to the cache, if error_found == false at the point when the message
// is reached.
// If is_error is true, the message will be considered an error msg,
// otherwise it is a progress msg.
void add_fol_message(const char *msg,   // handover, can be NULL
                     bool is_error,
                     enum HashType hash_type,
                     const uint8_t *hash);


// Update the status of all FOL problems -- this will check for completed
// child processes and launch any new ones required. This does not block.
// (Note: this is called automatically as part of solve_fol_problem.)
void update_fol_status();


// Block until the FOL problem queue is emptied.
// (It is safe to call this even if FolRunner wasn't started.)
void wait_fol_complete();


// Returns true if any error has been observed from any of the child
// processes so far. (This doesn't update status, it is just checking a flag.)
bool fol_error_found();

#endif
