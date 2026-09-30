# Plan: type inference for ghost arguments

Status: proposal (30-Sep-2026). Nothing described here is implemented.

This plan changes how type arguments are inferred at a call that has `ghost`
parameters. It covers the C compiler (`src/`), which already has ghost
parameters, and the Isabelle elaborator (`isabelle/`), which does not have
them yet; the Isabelle part describes how the call case must be built when
they are added.

Summary of the rule:

> In an executable call, a ghost actual is type-checked *against* the
> call's type arguments but never *determines* them. The type arguments
> must be fixed by the non-ghost actuals, by the surrounding statement, or
> by writing them explicitly.

Inside ghost code nothing changes.

## 1. Background

### 1.1 Ghost parameters and runtime types

A function parameter can be marked `ghost`. The corresponding actual is
ghost code: it may read ghost variables and have a non-runtime type (`int`,
`real`, a ghost abstract type), and it is erased before code generation.
This holds even when the call itself is executable:

```
function k(ghost z: int) {}

function test() {
    ghost var n: int = int(1);
    k(n);      // executable call, ghost actual of type int
}
```

Type arguments are different. The type arguments of an executable call
exist at run time (they are passed as sizes), so they must be *runtime
types*. Core states this directly: in `NotGhost` mode the rule for
`CoreTm_FunctionCall` requires `list_all (is_runtime_type env) tyArgs`
(`isabelle/core/CoreTypecheck.thy:357`). This is true even for a type
parameter that is only used in a ghost parameter's type.

So at an executable call with a ghost actual, two modes meet. The call's
type arguments belong to executable code; the ghost actual belongs to ghost
code. The question is what happens when type inference connects them:

```
function f1<T>(ghost z: T) {}

function test() {
    ghost var n: int = int(1);
    f1(n);     // T := int would be a non-runtime type argument
}
```

### 1.2 Other rules this plan relies on

These are already in force in both implementations:

* **Inference is per statement and nothing is defaulted.** A type
  metavariable that is still unresolved at the end of the statement that
  created it is an error ("Unable to infer type").
* **Metavariables range over complete types.** Unification never binds a
  metavariable to a type that is, or contains, an incomplete array type
  (`T[]`). This rule is independent of ghost mode, so it is not affected
  by anything below.

### 1.3 How the C handles it today

* Each univar carries a `must_be_executable` flag, set from
  `tc_context->executable` when the univar is created (`new_univar_type`,
  `src/typechecker.c:528`).
* When a univar is bound, the bound type is checked against that flag
  (`update_univar_type`, `:654`).
* If a type being checked for executability contains an unresolved univar,
  the flag is switched on for that univar (the `TY_UNIVAR` case of
  `ensure_type_meets_flags`, `:557`). This is *flag propagation*.
* In `nr_typecheck_call`, each actual is type-checked with
  `executable = false` if its formal is ghost (`:2158`). The loop that then
  matches actuals against formal types (`:2228`) runs in source order and
  entirely in the ambient mode.

Current behaviour, confirmed on `main` (30-Sep-2026):

```
datatype Maybe<a> = Nothing | Just(a);
function f1<T>(ghost z: T) {}
function f2<T>(x: T, ghost z: T) {}
function f3<T>(ghost y: Maybe<T>, ghost z: Maybe<T>) {}
function f4<T>(ghost y: Maybe<T>): Maybe<T> { return Nothing; }

function test() {
    ghost var g: i32 = 1;
    ghost var n: int = int(1);
    var v: i32 = 2;
    f1(g);                             // accepted, T := i32 from the ghost actual
    f2(v, g);                          // accepted
    f3(Nothing, Just(g));              // accepted, T := i32 from the ghost actual
    var m: Maybe<i32> = f4(Nothing);   // accepted
    f1(n);                             // rejected: 'int' or 'real' types not allowed
    f1<i32>(g);                        // accepted
}
```

No unsoundness is known in this scheme. The reasons to replace it are:

* **It is fragile.** The flag is mutable state that has to be carried
  correctly from univar to univar every time one is bound to a type
  containing another. It has already been wrong once: the `TY_UNIVAR` case
  used to overwrite the flag instead of merging it, so
  `f2(h(), n)` with `f2<T>(ghost y: Maybe<T>, ghost z: T)` and
  `h<U>(): U` was accepted at `T := int`
  (`test/cases/typechecker/UnivarFlags.b` is the regression test).
* **It has no simple counterpart in the Isabelle.** See 1.4. The Isabelle
  defines the language, so the C should implement whatever rule the
  Isabelle can state and prove.

### 1.4 Why the Isabelle needs a design

The Isabelle elaborator has no ghost parameters today: `DF_TmArgs`
(`bab/BabSyntax.thy`) and `FI_TmArgs` (`core/CoreTyEnv.thy`) carry no ghost
flag, and `elab_term` never changes its `ghost` argument on recursion.

Its proof that inferred type arguments are runtime types depends on that.
`elab_term_correct` types the elaborated term in
`extend_env_with_tyvars env ghost next_mv next_mv'`
(`elaborator/ExtendEnvWithTyvars.thy:9`), which adds *every* metavariable
of the interval `[next_mv, next_mv')` to `TE_TypeVars`, and in `NotGhost`
mode also to `TE_RuntimeTypeVars`. In other words: all metavariables of a
term are runtime type variables, or none are, according to the single mode
the term was elaborated in. Every unification binding is then a runtime
type because both sides of every unification problem were typed in that
one mode.

A ghost actual inside a `NotGhost` call breaks the "single mode" premise.
Its metavariables must not be assumed runtime, and its type can be `int`.
If the actual's type were simply unified against the formal type with
every metavariable flexible (as `unify_and_coerce` does today, with
`is_flex = (λn. n |∉| TE_TypeVars env)`), then `f1(n)` would produce
`?T := int` and the emitted call would fail Core's `is_runtime_type`
condition. Worse, a check keyed on the mode at binding time can be
laundered: `?U := Maybe<?T>` in ghost mode, or `?T := ?U` in executable
mode followed by `?U := int` in ghost mode, change what `?T` denotes
without `?T` itself being bound in the wrong mode.

Reproducing the C's flags in the Isabelle would mean tracking a mode per
metavariable through `unify` and re-establishing it in every proof about
substitutions. The design below avoids that: every unification problem
again has all its flexible metavariables in one mode.

## 2. Design

### 2.1 The rule

An executable call is processed in this order.

1. **Create the call's metavariables.** Omitted type arguments become fresh
   metavariables (`?T`), as today.

2. **Process the non-ghost actuals.** Elaborate each in `NotGhost` mode and
   unify its type against the formal type, with all metavariables flexible.
   This is today's behaviour. Both sides are executable-mode types, so
   every binding is a runtime type.

3. **Process each ghost actual as a closed unit.**
   1. Elaborate it in `Ghost` mode. Any metavariables it creates (`?U`)
      are its own.
   2. Unify its type against the formal type, with the substitution from
      step 2 applied. Only the actual's own `?U` are flexible; every other
      metavariable, in particular the call's `?T`, is *rigid* (treated as
      an opaque type).
   3. Apply the resulting substitution to the actual's term.
   4. If any `?U` remains in the term, fail with "Unable to infer type".

4. **Finish the statement as usual.** A `?T` that is still unresolved can
   be bound by the rest of the statement (for example by the declared type
   in `var m: Maybe<i32> = f4(Nothing)`), in the statement's own mode. If
   it is still unresolved at the end of the statement, the existing
   per-statement check rejects it.

When the ambient mode is already `Ghost` (a ghost function, a ghost
statement, an `assert`, an attribute, ...) a ghost parameter is not
special: all actuals are elaborated and unified in `Ghost` mode exactly as
today, and ghost actuals can determine type arguments.

### 2.2 Why this is enough

Inference communicates only through metavariables, and there are two
kinds:

* **The actual's own `?U`.** They occur only in that actual's term. Each is
  either resolved by the actual's own unification (step 3.2) or rejected
  (step 3.4), so none is alive when anything else is processed.
* **The call's `?T`.** They are shared by all the actuals, but they are
  rigid in step 3.2, so a ghost actual can mention them and cannot bind
  them.

So information flows into a ghost actual and never out of it. Every
binding of a `?T` is made in `NotGhost` mode from executable-mode types,
which restores the premise of the runtime-type argument in 1.4. The
laundering cases cannot arise: `?U := Maybe<?T>` is harmless because it
leaves `?T` alone, and `?T := ?U` cannot happen because no `?U` ever
appears in a type that a `NotGhost` unification sees.

There is also an erasure argument for the rule, independent of the proofs.
A type argument of an executable call is runtime data. If a ghost actual
can determine it, as in `f1(g)`, then ghost code decides a value that the
compiled program passes. Under this rule the executable part of a call
elaborates the same way whatever the ghost actuals are: they can cause the
call to be rejected, but they cannot change what it means.

Two consequences of step 3.2 worth spelling out:

* A ghost actual can end up *mentioning* `?T`. With formal `Maybe<?T>` and
  actual `Nothing : Maybe<?U>`, unification gives `?U := ?T`. That is why
  step 3.4 looks only for leftover `?U`, not for all metavariables; the
  `?T` is dealt with in step 4.
* Non-ghost actuals go first so that `?T` has its best chance of being
  resolved before a ghost actual is compared with it. A ghost actual of
  type `i32` unifies with formal type `T` only if `?T` is already `i32`.

### 2.3 What users lose

With the declarations from 1.3:

| Call | Today (C) | Under this plan |
|---|---|---|
| `f1(g)` | accepted | rejected; write `f1<i32>(g)` |
| `f2(v, g)` | accepted | accepted (`T` from `v`) |
| `f3(Nothing, Just(g))` | accepted | rejected; write `f3<i32>(...)` |
| `var m: Maybe<i32> = f4(Nothing)` | accepted | accepted (`T` from the declared type) |
| `f1(n)` | rejected | rejected (different message, see 5) |
| `f1<i32>(g)` | accepted | accepted |

So the cost is that an executable call's type arguments can no longer be
inferred from ghost actuals alone. A single-line search of `packages/` and
`test/cases/` for generic functions with a ghost parameter finds only
`UnivarFlags.b`, so the practical cost is expected to be nil; step 0 of 4
measures it properly.

### 2.4 Alternatives considered

* **Keep flag propagation in the C and mirror it in the Isabelle.** Accepts
  more programs (`f1(g)`). Rejected for the reasons in 1.3 and 1.4: it
  needs a per-metavariable mode in the Isabelle unifier and its proofs.
* **Let a ghost actual bind `?T` freely and check at the end of the
  statement** that every executable call's type arguments are runtime
  types. Because inference is per statement and nothing is defaulted, the
  term is ground by then, so this check is well defined and cannot be
  laundered; it would accept the same programs as the C does today. The
  objection is to the proof, not the definition. `elab_term_correct` keeps
  the term well-typed in Core at every intermediate stage, and Core's
  `NotGhost` call rule demands runtime type arguments. A term such as
  `f1<?T>(n)` followed by `?T := int` is not well-typed after the
  substitution, so the invariant would have to be weakened to "well-typed
  apart from runtime-ness" throughout `elab_term_correct` and the
  substitution-preservation lemmas, with runtime-ness recovered separately
  at the statement level. That is a second typing judgment in all but
  name. This size estimate is a judgement; it has not been tried.
* **Stricter closing: require the ghost actual to mention no metavariable
  at all after step 3.3.** Simpler to state (it is what `while` invariants
  do, with `term_inferred env`), but it rejects `f4(Nothing)` and any ghost
  actual checked before `?T` is resolved by the surrounding statement.
  Not chosen; step 3.4 checks the actual's own metavariables only.

## 3. Isabelle

### 3.1 Prerequisite (not part of this plan)

Ghost parameters must exist: a ghost flag on `DF_TmArgs` and `FI_TmArgs`;
Core's call rules type the actual for a ghost formal in `Ghost` mode and
require runtime types only of non-ghost formals; the interpreter ignores
ghost actuals. This plan only fixes how the elaborator's call cases infer
types once that is in place. Data constructors have no ghost fields and
are unaffected.

### 3.2 Definitions

Affected: the `BabTm_Call` case of `elab_term`
(`elaborator/ElabTerm.thy:924`) and `elab_impure_call_term`
(`elaborator/ElabStmt.thy:107`). Both currently do

```
elab_term_list env elabEnv ghost args next_mv1
unify_and_coerce (λn. n |∉| TE_TypeVars env) locOf elabArgTms actualTypes expArgTypes fmempty
```

When `ghost = Ghost`, or the callee has no ghost formals, that stays
exactly as it is. When `ghost = NotGhost` and some formal is ghost:

1. **Elaborate the actuals with a mode per argument.** A variant of
   `elab_term_list` that takes the list of formal ghost flags, elaborates
   the actual for a ghost formal in `Ghost` mode and the others in
   `NotGhost`, and returns for each ghost actual the counter interval
   `[lo_i, hi_i)` it consumed. Elaboration order stays the source order;
   only the unification order changes.

2. **Unify the non-ghost actuals** with `unify_and_coerce` and the usual
   `is_flex`, giving `accSubst` and the coerced non-ghost terms.

3. **For each ghost actual** with term `tm`, type `actualTy`, interval
   `[lo, hi)` and formal type `formalTy`:
   * `expectedTy = apply_subst accSubst formalTy`;
   * unify (up to coercion, inserting the coercion as usual) `actualTy`
     against `expectedTy` with
     `is_flex = (λn. n |∈| mv_fset lo hi)`; on failure,
     `TyErr_TypeMismatch`;
   * `tm' = apply_subst_to_term s tm` for the resulting `s`;
   * if `¬ list_all (λn. n |∉| mv_fset lo hi) (core_term_free_tyvars_list tm')`
     then `TyErr_CannotInferType` at the actual's location.

   `s` is *not* composed into `accSubst`. Its domain is inside
   `[lo, hi)`, and those names occur nowhere else.

4. **Build the result** from `accSubst` as today (`build_call_result`, or
   the tuple returned by `elab_impure_call_term`), with the ghost actuals'
   `tm'` in their argument positions. The terms `tm'` may still mention the
   call's metavariables; the final substitution applied by the enclosing
   statement covers them like any other part of the term.

The completeness wrapper around unification applies to the ghost actual's
unification as to any other.

`check_ref_args` in `elab_impure_call_term` needs the ghost actuals'
substituted types; use `apply_subst s actualTy` for those positions.

### 3.3 Proof

The statement of `elab_term_correct` can stay as it is: the result is
typed in `extend_env_with_tyvars env ghost next_mv next_mv'`. What changes
is the call case (`elab_term_correct_call`,
`elaborator/ElabTermCorrect.thy:125`, and the impure-call counterpart).

For a ghost actual in a `NotGhost` call:

* The induction hypothesis, used at mode `Ghost`, types `tm` in
  `extend_env_with_tyvars env Ghost lo hi` in `Ghost` mode.
* `s` has domain inside `mv_fset lo hi` (from the `is_flex` used) and a
  range that is well-kinded in the env extended with the call's
  metavariables. Substitution preservation types `tm'` at
  `apply_subst s actualTy` in the env extended with both blocks.
* By the check in step 3, `tm'` mentions no name of `mv_fset lo hi`, so
  `core_term_type_remove_unused_tyvars` (`core/CoreTypecheck.thy:1824`)
  removes that block from the env.
* The remaining env differs from the target
  `extend_env_with_tyvars env NotGhost next_mv next_mv'` only by having
  fewer type variables and fewer runtime type variables. `Ghost`-mode
  typing is monotone in both. (A lemma "growing `TE_TypeVars` and
  `TE_RuntimeTypeVars` preserves `core_term_type env Ghost`" is needed if
  not already available in this form; the `is_runtime_type` half exists in
  `core/CoreTypeProps.thy:195`.)

For the type arguments: `accSubst` comes only from step 2, so the existing
argument that its range is runtime in `NotGhost` mode applies unchanged.
That is the point of the design.

The statement-level lemmas are unaffected: a statement still applies one
final substitution and checks `term_inferred` / `call_inferred`.

## 4. C compiler

All changes are in `src/ast.h` and `src/typechecker.c`. The C has no
intervals and no `is_flex`; "rigid" is expressed as a rule about which mode
may bind a univar.

0. **Measure.** Before anything else, make the change in steps 1-5 and run
   `make check` and `make packages` to see what stops compiling. If real
   code depends on inferring from ghost actuals, revisit 2.4.

1. **Creation-mode bit.** In `struct UnivarNode` (`src/ast.h:61`) replace
   `must_be_executable` by

   ```c
   bool executable;  // Mode in which the univar was created. It can only be bound in the same mode.
   ```

   set once in `new_univar_type` from `tc_context->executable` and never
   changed.

2. **Refuse cross-mode bindings.** Add

   ```c
   // A univar can only be bound in the mode (executable or ghost) that created it.
   static bool univar_is_bindable(struct TypecheckContext *tc_context, struct Type *type)
   {
       return type->univar_data.node->executable == tc_context->executable;
   }
   ```

   and choose the direction in `unify_types` (`:716-733`) accordingly:

   ```c
   bool expected_flex = expected_type->tag == TY_UNIVAR && univar_is_bindable(tc_context, expected_type);
   bool actual_flex = actual_type->tag == TY_UNIVAR && univar_is_bindable(tc_context, actual_type);

   if (expected_type->tag == TY_UNIVAR && actual_type->tag == TY_UNIVAR
   && actual_type->univar_data.node == expected_type->univar_data.node) {
       // expected_type and actual_type are the same variable. Do nothing.
       return true;
   }

   if (expected_flex) {
       // Set expected := actual.
       return update_univar_type(tc_context, expected_type, actual_type, loc);
   }

   if (actual_flex) {
       // Set actual := expected.
       return update_univar_type(tc_context, actual_type, expected_type, loc);
   }

   // If we get here, any remaining univar is rigid (it was created in the
   // other mode), and is treated like any other type.
   ```

   Formal `?T` against a ghost actual's `?U` then binds `?U := ?T`, as the
   Isabelle does. In the rest of `unify_types`, a rigid univar against a
   non-univar already reaches the tag-mismatch branch; two different rigid
   univars reach `case TY_UNIVAR` (`:867`), which changes from a
   `fatal_error` to `ok = false`.

   `update_univar_type` additionally asserts `univar_is_bindable` on its
   `lhs`.

3. **Derive the requirements from the current mode.** In
   `update_univar_type` (`:666`):

   ```c
   struct TypeFlags flags = {
       .must_be_executable = tc_context->executable,
       .must_be_complete = true
   };
   ```

   By step 2 this equals the univar's bit.

4. **Delete the propagation.** The `TY_UNIVAR` case of
   `ensure_type_meets_flags` (`:557`) no longer writes to the univar. An
   unresolved executable univar will be checked when it is bound, by
   step 3. A ghost univar inside a type that is required to be executable
   should be impossible (2.2); make that case a `fatal_error` first, and
   turn it into an ordinary error only if it proves reachable.

5. **Reorder the matching loop** in `nr_typecheck_call` (`:2228`) into two
   passes: non-ghost formals in the ambient mode, then ghost formals with
   `tc_context->executable = false` around `match_term_to_type`. The `ref`
   checks in that loop read `tc_context->executable` (`:2253`) and must
   stay outside the mode switch; move them into a helper called from both
   passes.

   The loop at `:2158` that type-checks ghost actuals in ghost mode is
   unchanged. In a ghost context both passes run with
   `executable = false`, every univar has the ghost bit, and the behaviour
   is the same as today.

6. **No closing step per actual.** A ghost actual's leftover univar is
   rejected by the per-statement check
   (`single_statement_contains_unresolved_univars`), which reports "Unable
   to infer type" at the univar's own location. This gives the same set of
   accepted programs as the Isabelle's step 3.4.

Audit of the other places that switch `tc_context->executable`
(`obtain` `:3240`, `assert` `:3402`, `assume` `:3441`, `while` attributes
`:3472`, ghost statements `:3592`, function attributes `:3998`): each
type-checks *and* unifies inside the ghost window, so no univar is created
in one mode and bound in the other. The call-argument loop is the only
site where that happened, and step 5 removes it.

`struct TypeFlags` and the explicit `must_be_executable` checks at
declaration sites are unchanged.

## 5. Error messages

A ghost actual that fails against a rigid `?T` (for example `f1(g)`) is a
unification failure. In the Isabelle that is `TyErr_TypeMismatch`; in the
C it reaches `report_type_mismatch` with an unresolved univar as the
expected type. Neither tells the user what to do. Proposed: when the
mismatch involves a rigid metavariable, report a dedicated error along the
lines of "cannot infer type argument from a ghost argument", at the
actual's location, in both implementations. To be decided when
implementing (see 7).

## 6. Tests and documentation

* `test/cases/typechecker/UnivarFlags.b`: rename or rework. `f1(n)` and
  `f2(h(), n)` stay errors with new messages; the comments about flags go.
* New typechecker cases (the table in 2.3): inference from a ghost actual
  alone is rejected; a non-ghost actual or the statement context fixes `T`
  and the ghost actual is then checked against it, including a mismatch
  (`f2(v, b)` with `b: bool`); `?U := ?T` direction (`f4(Nothing)` with a
  declared result type); a leftover ghost univar (`k(h())` with `k(ghost z: int)`
  and `h<U>(): U` is fine, but a ghost actual with a phantom type argument
  is "Unable to infer type"); explicit type
  arguments; the same calls inside a ghost function, where inference from
  ghost actuals still works.
* `docs/lang-ref.md`, "Function calls": state the rule from the top of
  this document next to the existing per-statement inference rule.

## 7. Open questions

* The wording and form of the error in 5.
* Whether the Isabelle should express rigidity by interval (3.2) or by
  "not a type variable of the expected type". The interval form matches
  how the proof removes the block afterwards and is preferred unless it
  proves awkward.
* Whether the monotonicity lemma in 3.3 exists in a usable form.
