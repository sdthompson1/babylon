# Proposal: ghost code by erasure

Status: adopted, and implementation has started (1-Oct-2026). Stages 0,
1 and 2 are done (2-Oct-2026); section 11 records what exists and what
comes next. This plan replaces section 3 of `GHOST_ARGS.md` (see
section 7 below). The uncommitted ghost-parameter work is parked on the
branch `ghost-args`.

Agreed so far (1-Oct-2026):

* ghost markers stay in the Core syntax, and the Core typechecker and
  interpreter ignore them (3.2);
* the ghost rules, the erasure pass and their theorems form a separate
  layer, `core_ghost`, above Core (3.6);
* the interpreter stays a fuel-based function, with two-level fuel
  (3.5);
* the ghost rules are called *well-ghosted*, by analogy with
  well-typed, and are a family of definitions like the typing ones
  (3.2);
* all the questions of section 9 are decided; question 3 (`Assume`)
  provisionally.

Items marked **(unverified)** are claims I believe but have not checked
against Isabelle or proved.

Summary:

> Core stops having two typing modes. Ghost code gets a real semantics:
> the interpreter runs it. A separate judgment, well-ghosted, says which
> code is ghost and that ghost code cannot influence executable code. A
> Core-to-Core
> pass, `erase_ghost`, deletes the ghost code. A simulation theorem says that
> if the full program runs to completion, the erased program runs to
> completion with the same result.

## 1. Background

### 1.1 How Core handles ghost code today

* **Typing has two modes.** `core_term_type` and `core_statement_type`
  take a `GhostOrNot` argument. `NotGhost` mode adds restrictions: no
  ghost variables, runtime type arguments, no quantifiers, equality only
  at bool and numeric types, and so on. Statements carry their own
  markers (`CoreStmt_VarDecl Ghost ...`), and the environment tracks
  `TE_GhostLocals`, `TE_RuntimeTypeVars`, `TE_GhostDatatypes` and
  `TE_FunctionGhost`.
* **The interpreter skips ghost code.** A `Ghost`-marked `VarDecl`,
  `Assign`, `Swap`, `While` or `Match` is a no-op
  (`interpreter/CoreInterp.thy:745`, `:816`, `:854`, `:873`, `:888`).
  `Assert`, `Assume` and `Obtain` are ignored (`:902`-`:913`).
  Quantifiers, `allocated` and `old` are a `TypeError` (`:669`).
  `IS_Functions` holds only non-ghost functions.
* **Values are runtime values only.** `CoreValue` has no `int` or `real`
  (`core/CoreValue.thy:13`).
* **Type soundness covers `NotGhost` only**
  (`interpreter/TypeSoundness.thy:16`). `state_matches_env` lets a ghost
  local be absent from the state.

Two observations follow.

1. Today's interpreter is already an erased semantics: it computes what
   the program does with the ghost code removed, deciding what to remove
   as it goes.
2. Ghost code has no meaning in the model. An `assert` does nothing, so
   no statement of the form "a verified program does not fail" can be
   written down.

### 1.2 Why change

* The ghost-parameter work in `GHOST_ARGS.md` became complicated in the
  interpreter and soundness layer. Skipping a ghost actual means the
  argument-binding fold, the extern contract and the soundness
  induction all need a per-parameter case split.
* The eventual goal is a verifier and a code generator. The claim we
  want is the chain in section 2, and its first link needs a semantics
  for ghost code.

## 2. The target claim

1. The verifier accepts a program. Trusting the SMT solvers, the full
   program (ghost code included) runs to completion without error.
   This step is informal.
2. Therefore the erased program runs to completion without error and
   with the same result. This step is proved in Isabelle (section 6).
3. Therefore the generated C behaves the same way. This is the future
   code-generator theorem, stated against the erased program.

The chain rests on three properties of Core code:

| Property | Established by | What it gives |
|---|---|---|
| well-typed | the elaborator, whenever it succeeds (theorem 1 of section 4) | no `TypeError` (theorem 3) |
| well-ghosted (3.2) | the elaborator, whenever it succeeds (theorem 2) | erasure preserves typing and results (theorems 4 and 5) |
| well-verified | the verifier, as a separate step | the full program runs to completion without error (step 1) |

The first two are static checks on the program text. The third is
not: it depends on the SMT solvers, and this document treats it
informally.

## 3. Design

### 3.1 Core typing has one mode

`core_term_type env tm` and `core_statement_type env stmt` lose the
`GhostOrNot` argument and every `ghost = NotGhost ⟶ ...` side
condition. What remains is today's `Ghost`-mode typing, minus the rule
that everything inside a ghost statement must itself be marked ghost.

### 3.2 Where the ghost rules go: `well_ghosted`

The rules do not disappear. The simulation proof needs to know:

* which locals are ghost;
* that executable code never reads a ghost local;
* that ghost statements write only to ghost lvalues
  (`ghost_lvalue_ok`, `core/CoreTypeProps.thy:279`);
* that ghost statements do not return from a non-ghost function;
* that ghost statements do not change `IS_World`;
* that executable code uses only runtime constructs (the old
  `NotGhost` restrictions).

So the proposal keeps the ghost markers in the Core syntax, where
typing and the interpreter ignore them, and adds a second static
judgment, *well-ghosted*, which carries the rules above. The name is
by analogy with well-typed: a check on the program text that
guarantees something about its runs. For well-typed that is "no
`TypeError`"; for well-ghosted it is "erasing the ghost code keeps the
result" (section 6).

Like typing, it is a family of definitions, one beside each typing
definition:

| Well-ghosted | Typing counterpart |
|---|---|
| `core_term_well_ghosted` | `core_term_type` |
| `core_statement_well_ghosted` | `core_statement_type` |
| `core_statement_list_well_ghosted` | `core_statement_list_type` |
| `core_module_well_ghosted` | `core_module_well_typed` |

In the rest of this document `well_ghosted` means whichever of these
applies. Their shapes follow the typing definitions:

* The term and statement versions take the ambient mode
  (`GhostOrNot`), as the typing definitions do today. Stage 2 of
  section 10 can then state "old judgment = one-mode typing +
  well-ghosted" at the same mode.
* The statement versions thread a context, because a `VarDecl` changes
  the ghost-local set. Either they return the updated context (as
  `core_statement_type` returns a `CoreTyEnv option`), or they are
  predicates and a separate function computes the context after a
  statement. To be settled when they are written.
* They call `core_term_type` where a rule needs a type (the equality
  rule does), so the statement versions also need the `CoreTyEnv` at
  each program point. Well-ghosted is only meaningful for well-typed
  code.

Ghost information is of two kinds, and they go to different places.

* **Markers on declarations and statements** stay where the thing is
  declared, and Core ignores them: the `GhostOrNot` on the six
  statement constructors, `FI_Ghost`, and the per-parameter flag in
  `FI_TmArgs`. Keeping the function flags inside `FunInfo` avoids a
  parallel table that would have to be kept consistent with
  `TE_Functions`.
* **Context that today's typing threads** leaves `CoreTyEnv` and
  becomes a context of `well_ghosted`: the ghost-local set
  (`TE_GhostLocals`) and the ambient function mode
  (`TE_FunctionGhost`). The typing rules stop updating them, and the
  `*_irrelevant` lemmas about them go away.

`TE_RuntimeTypeVars` and `TE_GhostDatatypes` are in between; see
question 9.

`executable` is then the special case: well-ghosted, and containing no
ghost code at all. The second half is a purely syntactic check,
`ghost_free`, and it is the half that needs its own family:

| Definition | Says |
|---|---|
| `core_statement_ghost_free`, `core_statement_list_ghost_free` | the statement has one of the erased forms of 3.3: no `Ghost` marker; no `Obtain`, `Assert`, `Assume`, `ShowHide`, `Fix` or `Use`; a `While` has no invariants and a trivial `decreases`; nested statements likewise |
| `core_module_ghost_free` | no ghost function, ghost parameter or ghost datatype; every function body is ghost-free |

There is no term version. A `CoreTerm` carries no markers and contains
no statements, so an "executable term" is one that is
`core_term_well_ghosted` at `NotGhost` mode. `executable` at each level
is the conjunction of well-ghosted and ghost-free, so it needs no
recursive definitions of its own.

The two halves do different jobs. Well-ghosted allows quantifiers and
other non-runtime constructs, but only in ghost positions. Ghost-free
says there are no ghost positions left. Together they give: an
executable program contains no non-runtime construct anywhere.

The gain is that the ghost rules leave the typing judgment and the type
soundness proof. The cost is that every Core transformation
(substitution, linking, match compilation) needs a "preserves
`well_ghosted`" lemma next to its "preserves typing" lemma.

### 3.3 `erase_ghost`

A Core-to-Core pass, in the style of `core_passes/MatchCompile*`.

| Construct | Erased form |
|---|---|
| `Ghost`-marked `VarDecl`, `VarDeclCall`, `Assign`, `AssignCall`, `Swap`, `While`, `Match` | removed |
| `Obtain`, `Assert`, `Assume`, `ShowHide`, `Fix`, `Use` | removed |
| `NotGhost` `While` | invariants dropped, `decreases` replaced by a trivial term, body erased |
| `NotGhost` `Match`, `Block` | bodies erased |
| Call (term or statement) | actuals for ghost parameters dropped |
| Function | ghost functions removed; ghost parameters removed from `FI_TmArgs` and `CF_Args` |
| Datatype | ghost datatypes removed |

`erase_ghost` needs the function table, to know which actuals to drop. This
is why the `GhostOrNot` flag on `FI_TmArgs` (commit c13f68e) stays.

A ghost declaration may shadow a non-ghost local. After erasure the
outer name is visible again in that region, but `well_ghosted` guarantees
no executable code refers to it there.

### 3.4 The interpreter runs everything

There is one interpreter. It ignores ghost markers and has no mode
argument. It is no longer executable (no Haskell export).

| Construct | Behaviour |
|---|---|
| `VarDecl`, `Assign`, `Swap`, `While`, `Match` | executed whatever the marker |
| Loop invariants | evaluated each time the loop condition is about to be tested; false is `RuntimeError` (question 4) |
| `decreases` | not evaluated |
| Call | ghost parameters are bound like any other; ghost functions are callable |
| `int`, `real` | new `CoreValue` constructors; arithmetic is unbounded |
| Equality | at any type, as HOL equality on values |
| Quantifier | see 3.5 |
| `Obtain x T P` | picks a value satisfying `P` (`SOME`); `RuntimeError` if there is none |
| `Assert c proof` | evaluates `c`; false is `RuntimeError`; the proof body is not run |
| `Assume c` | no-op, as now; `c` is not evaluated (provisional, question 3) |
| `Fix`, `Use` | `TypeError`, as now (they occur only in proof bodies) |
| `ShowHide` | no-op |
| `allocated` | always `false` for now; the real definition needs the operand's type (see 11.5, sub-step 9) |
| `old` | the identity, until Core has postconditions |

Extern functions need no special treatment in the full run. An extern
function cannot be ghost (`docs/lang-ref.md`, "Extern functions") and
cannot have ghost parameters (question 6), so a call to one binds and
passes exactly what it does today.

`process_one_arg` goes back to having no ghost case. The interpreter
half of the uncommitted ghost-parameter work is not needed.

### 3.5 Fuel and quantifiers

**The problem.** A natural reading of a quantifier is "evaluate the
body for every value and take the HOL `∀`". With one fuel counter the
body must be evaluated at `fuel - 1` for every value, so one fuel has
to suffice for all of them. That fails for

```
ghost function pow(b: int, n: int): int { ... a while loop running n times ... }

assert forall (n: int) n >= 0 ==> pow(2, n) > 0;
```

No fuel covers every `n`, so the quantifier would be `InsufficientFuel`
at every fuel. Since the language has no recursion
(`docs/lang-ref.md:93`), loops are the only way to write such
functions, so this is the common case rather than a corner.

**The proposal: two-level fuel.** The interpreter takes a pair
`(d, fuel)`. Every existing case passes `d` through and recurses on
`fuel` exactly as now. Only the quantifier case decrements `d`, and in
return evaluates each instance at whatever fuel that instance needs:

```
| "interp_term 0 (Suc _) _ (CoreTm_Quantifier _ _ _ _) = Inl InsufficientFuel"
| "interp_term (Suc d) (Suc _) state (CoreTm_Quantifier q x ty body) =
     combine q (λv. converged (λm. interp_term d m (bind x v state) body))"
```

* `converged f` is `f` at the least `m` where `f m` is not
  `InsufficientFuel`, or `InsufficientFuel` if there is no such `m`.
* `combine q r` ranges over the values of type `ty`:
  1. if some instance is `InsufficientFuel`, the result is
     `InsufficientFuel`;
  2. otherwise, if some instance is an error, the result is that error
     (`TypeError` before `RuntimeError`);
  3. otherwise the result is the HOL `∀` or `∃` of the instances.
* Termination is the lexicographic order on `(d, fuel)`. In ordinal
  terms the fuel is `ω·d + fuel`.

The order of the three steps in `combine` matters. Fuel monotonicity
says that once a result is not `InsufficientFuel` it never changes. If
a false instance could decide a `forall` while another instance was
still out of fuel, that other instance might turn into an error at a
higher depth and change the answer. Requiring every instance to be
defined first avoids this. `Obtain` needs the same rule, so that the
set `SOME` chooses from is fixed.

"The program terminates with result `r`" becomes
`∃d fuel. interp d fuel ... = Inr r`.

What is kept: the interpreter is still a function, so it is
deterministic for free, and each case still reads as "what the
language does".

What it costs in proofs: every lemma about the interpreter gains a `d`
that is passed through. Fuel inductions become a strong induction on
`d` around the existing induction on `fuel`; the outer hypothesis is
used only in the quantifier and `Obtain` cases. Executable code never
reaches those cases, so for it `d` is irrelevant.

The function package accepts the recursive calls under `λm` and `λv`
without a congruence rule, because the termination condition needs no
context beyond `d < Suc d`. This was confirmed by the toy theory of
stage 0 and again by the real definition (section 11).

**The limit of two-level fuel.** `d` bounds how deeply quantifier
evaluations nest at run time, and the bound must be the same for every
instance. Without recursion the nesting is bounded statically
(syntactic nesting plus the acyclic call graph), so a `d` always
exists. Section 8 covers what changes if recursion is added.

**Alternatives.**

* *One nat fuel, accept the gap.* Rejected: the example above is
  ordinary specification code.
* *General ordinal fuel.* Correct for everything. Loses the `Suc fuel`
  patterns, gives every induction a limit case, and needs an ordinal
  library. The cost falls on every case instead of one.
* *Relational big-step semantics.* Infinite branching is free (a rule
  can have a `∀v` premise). But each error-propagation line becomes a
  rule, determinism needs a proof, divergence becomes "no derivation",
  and about 12,000 lines of fuel-induction proofs (the soundness files
  and `CoreInterpFuelMono.thy`) would be redone. CakeML moved from
  relational to clocked functional big-step for these reasons
  (reference 2).
* *Relational for ghost code, fuel for executable code.* Works, but
  gives one syntax two semantics. Two-level fuel makes it unnecessary.

### 3.6 Layering: Core and `core_ghost`

The design splits what is now "Core" into two layers.

* **Core** (`core/`, `interpreter/`, `core_passes/`): syntax, typing,
  the interpreter, type soundness, substitution, linking, match
  compilation. Nothing here reads a ghost marker.
* **`core_ghost`** (new directory, added to `isabelle/ROOT`):
  * the `*_well_ghosted` definitions and their context;
  * `ghost_free` and `executable`;
  * the predicates only the ghost rules use (`is_runtime_type`,
    `ghost_lvalue_ok`, `tyenv_var_ghost`), moved out of `core/`;
  * `erase_ghost`;
  * theorems 4, 5 and 6 of section 4.

Dependencies run one way: `core` → `interpreter` → `core_ghost` →
`elaborator`. `core_ghost` imports the interpreter because the
simulation theorem is about it. The elaborator imports `core_ghost`
because its own checks use the ghost predicates and its correctness
theorem states `well_ghosted`.

The test of the split is that a reader who wants to know what a Core
program means, or whether it is well-typed, never opens `core_ghost`.

## 4. Theorems

1. **Typing.** The elaborator's output is well-typed (one mode).
2. **Ghost discipline.** The elaborator's output is well-ghosted.
3. **Type soundness.** A well-typed program never produces `TypeError`.
   This now covers ghost constructs too.
4. **Erasure preserves typing.** If `p` is well-typed and
   well-ghosted, then `erase_ghost p` is well-typed and `executable`.
5. **Simulation.** Section 6.
6. **Transformations.** Substitution, linking and match compilation
   preserve `well_ghosted`, and `erase_ghost` commutes with them.

Theorems 1 and 2 together are what the elaborator proofs establish
today. Theorem 2 is proved, in the same way as theorem 1 (question 7).
The alternative, having the elaborator run `well_ghosted` on its
output and reject on failure, was not chosen.

## 5. The elaborator

The elaborator keeps its `ghost` argument, because the source-level
rules and error messages do not change. It emits one program, with
markers. It carries the `well_ghosted` context (the ghost-local set)
alongside the `CoreTyEnv`, since the latter no longer holds it.

The original version of this idea had the elaborator emit two
programs, the full one and the erased one, with no markers in Core.
That was considered and not chosen. The two programs have different
signatures
(ghost parameters and ghost functions are missing from one), so either
well-typedness is proved twice or a relation between the outputs is
threaded through the `ElabStmtCorrect` induction. With `erase_ghost` as a
Core pass, the elaborator proofs stay about one output and theorem 4
is proved once at Core level.

## 6. The simulation theorem

### 6.1 Statement

Informally: let `p` be well-typed and well-ghosted. If running `p`
from state `s` gives a normal result at some `(d, fuel)`, then running
`erase_ghost p` from the related state gives a normal result at the
same `(d, fuel)`, and the results are related.

The same fuel works because the erased program does strictly less, and
the interpreter is monotone in fuel.

### 6.2 Why "runs to completion" and not "never fails"

"The full program never fails, so the erased program never fails" is
false:

```
ghost while true { }
x = 1 / 0;
```

The full program never reaches the division; the erased program does.
Erasure is only sound for ghost code that terminates. So the theorem's
premise is that the full run terminates normally, and the verifier is
trusted for termination as well as safety. It already checks
`decreases`.

This is the easy direction of simulation: one forward induction on the
run of the full program, with no need to reason about divergence.

### 6.3 The state relation

The erased state is the full state restricted to non-ghost names.

* Globals, world and function tables correspond (the erased table holds
  the erased functions).
* Every non-ghost local is present in both states, with equal values.
* Ghost locals are absent from the erased state.

The one complication: the full run allocates store cells for ghost
variables (`alloc_store` appends, `CoreInterp.thy:321`), so addresses
differ between the two runs. The relation therefore includes an
order-preserving embedding of erased addresses into full addresses.
This is milder than it sounds:

* `CoreValue` contains no addresses, so related values are equal, not
  merely related;
* allocation is stack-like (`restore_scope` truncates the store), so
  the embedding only ever grows and shrinks at the end.

### 6.4 Main lemmas

* **Executable terms agree.** A term in executable position evaluates
  to the same value in both states. This is mutual with the lemma for
  calls.
* **Ghost statements are invisible.** Running a ghost statement in the
  full state leaves the relation intact against the unchanged erased
  state. This needs a footprint fact: a call changes only the cells
  reachable through its `ref` arguments, and in ghost code those are
  ghost cells.
* **Calls.** The callee's frames are related; the full frame has the
  ghost parameters bound, the erased frame does not have them.

### 6.5 Effort

The proof has the same shape as `type_soundness`: one mutual induction
over the six interpreter functions. My guess is a few thousand lines,
but this is the least certain number in this document. Section 10
puts this proof first for that reason.

## 7. Effect on the ghost-parameter work

* **Commit c13f68e** (the flag on `FI_TmArgs` and `IF_Args`): the
  `FI_TmArgs` flag stays. The `IF_Args` flag becomes unnecessary; it is
  inert as committed, so it can be removed whenever convenient.
* **Uncommitted interpreter and soundness changes:** not needed.
* **Uncommitted Core rules** (`args_typed` with per-argument modes,
  `param_mode`, the ghost-`ref` rule, the relaxed
  `tyenv_fun_ghost_constraint`): the content moves into `well_ghosted`.
* **Design decisions in `GHOST_ARGS.md` 3.1** (normalisation in
  `elab_fun_signature`, parser syntax): unchanged.
* **Ghost parameters on extern functions:** `GHOST_ARGS.md` allowed
  them. They are now forbidden (question 6).
* **Type-argument inference.** The requirement that an executable
  call's type arguments are runtime types does not go away; it becomes
  part of `well_ghosted`. But alternative 2 of `GHOST_ARGS.md` 2.4 becomes
  viable. It was rejected because intermediate terms such as
  `f1<?T>(n)` with `?T := int` are not well-typed in `NotGhost` mode.
  With one typing mode they are well-typed, and runtime-ness can be
  checked on the final term at the end of the statement. That would
  keep the C compiler's current behaviour (`f1(g)` accepted, `f1(n)`
  rejected) with no change to the C.

The uncommitted work should be parked on a branch rather than
discarded, in case this proposal is dropped.

**A gap that exists today, independent of this proposal.** The Isabelle
does not require a non-impure function to avoid impure calls (question
5; to be fixed in stage 6). Such a function can be called in term
position, where
`interp_term` discards the callee's final state on the grounds that
"pure functions don't change the state"
(`interpreter/CoreInterp.thy:597`). An impure call inside it would
have its world update silently dropped. Type soundness is unaffected,
but the Isabelle accepts programs the C rejects and gives them a
meaning the C would not.

## 8. If recursion is added later

Depth is spent once per quantifier, so it measures how deeply
quantifier evaluations nest. A recursive cycle that passes through a
quantifier body makes that nesting grow with the argument
(hypothetical syntax; recursion is not supported today):

```
ghost function f(k: int): bool
    decreases k;
{
    if k <= 0 { return true; }
    return forall (x: int) f(k - 1);
}
```

`f(k)` needs depth `k`. Any one call is fine. But
`forall (k: int) f(k)` evaluates every instance at the same depth, and
no finite depth covers all `k`. With an ordinal index, the quantifier
case would say "each instance may use any depth below mine", and depth
ω would work.

Two things must coincide for this: a recursive cycle through a
quantifier body, and an enclosing quantifier over the argument that
drives the recursion. Plain recursion is harmless; a recursive `pow`
uses ordinary fuel.

A `decreases` clause does not remove the problem. It guarantees each
call terminates but gives no bound uniform across instances (`f` has
one). With lexicographic tuples, a single call can already need
infinite depth:

```
ghost function g(a: int, b: int): bool
    decreases {a, b};
{
    if b > 0 { return forall (y: int) g(a, b - 1); }
    if a > 0 { return forall (x: int) x >= 0 ==> g(a - 1, x); }
    return true;
}
```

`g(0, x)` needs depth `x`, so the quantifier inside `g(1, 0)` needs ω,
and `forall a. g(a, 0)` needs ω².

What `decreases` does provide is a bound on which ordinals occur: the
clause maps each call into a well-order (ω^k for a k-tuple) and the
depth tracks that measure. **(unverified)** My estimate is that a
finite program with tuple-valued `decreases` clauses stays below ω^ω.
Such ordinals can be written as lists of nats, so no ordinal library
would be needed.

Options at that point:

* **Generalise the depth index** to any well-ordered type, with the
  quantifier case reading "some smaller depth". Only that case and the
  outer induction change. Nat depth is the instance used until then.
* **Restrict the language** so that no recursive cycle passes through
  a quantifier body. Nat depth stays sufficient. This rules out natural
  predicates over recursive datatypes, such as "every child of this
  node is valid" written with a `forall` over child indices.

## 9. Questions and decisions

Decisions are dated 1-Oct-2026. Question 3 is decided provisionally.

1. **Function package.** Does it accept the quantifier case of 3.5 as
   written?

   **Decided:** test it with a toy theory before anything else
   (stage 0).

   **Answer (1-Oct-2026):** yes. See section 11.
2. **Domain of quantification.** "All values of type `ty`" needs
   `value_has_type`, which takes a `CoreTyEnv`; the interpreter state
   has no constructor table.

   **Decided:** the interpreter state gains a constructor table (it
   already has `IS_DefaultCtors`, a table of the same kind). A detail
   to settle when it is written: `value_has_type` reads more than
   `TE_DataCtors`. It reads `TE_Datatypes` and `TE_TypeVars` through
   `is_well_kinded`, and `TE_GhostDatatypes` and the runtime-type test
   (`core/CoreValue.thy:61`). The runtime-type conditions have to go
   in any case, because ghost values now exist. So either the state
   carries the datatype arities as well, or the quantifier's domain is
   defined by a version of `value_has_type` over the state's tables.
3. **`Assume` when false.** An error (so the theorem's premise says the
   assumptions held), or a distinct outcome?

   **Decided, provisionally:** `Assume` stays a no-op, as it is today,
   and its condition is not evaluated. The choice does not affect
   anything in this plan: the simulation theorem holds either way, and
   nothing here defines well-verified or proves anything about it.

   To revisit when well-verified is defined. The verifier accepts
   `assume false; x = 1 / 0;`, so "well-verified implies no
   `RuntimeError`" cannot hold for every program while `Assume` is a
   no-op. The options then:
   * keep the no-op, or make a false `Assume` a `RuntimeError` like a
     false `Assert`, and state the claim only for programs with no
     `Assume`;
   * give a false `Assume` its own outcome (a fourth `InterpError`
     constructor, say `AssumptionFailed`). The claim then covers every
     program: a well-verified run ends normally or in
     `AssumptionFailed`, never in `RuntimeError`. The quantifier's
     `combine` rule (3.5) would need a rank for the new outcome.
4. **Loop invariants and `decreases`.** They are proof devices; the run
   terminating is the semantic fact. Should the interpreter check
   invariants anyway, so that they mean something?

   **Decided:**
   * loop invariants are checked, and a false one is `RuntimeError`;
   * `decreases` is not checked at run time;
   * `requires` and `ensures` conditions will be added to Core at some
     point, and will be checked in the same way (`RuntimeError` if
     false). `erase_ghost` will then drop them, and `ghost_free` will
     need a clause for them;
   * none of this is needed at the start. The checks can be added in a
     pass after the main work (stage 6), with the proofs updated as
     needed.
5. **Ghost calls to impure functions.** Checked 1-Oct-2026. In a full
   run, a ghost call that changed the world would break the
   simulation, because the erased run would not make it. The C
   compiler rules this out with three checks
   (`test/cases/typechecker/Impure.b`):
   * an impure function cannot be referenced from ghost code
     (`src/typechecker.c:1319`);
   * an impure function cannot be referenced from a function that is
     not itself `impure` (`:1324`);
   * a ghost function cannot be declared `impure` (`:3878`).

   Together these mean the world changes only through executable,
   statement-position calls, which is what the simulation needs.

   The Isabelle has none of the three. It rejects an impure call in
   term position (`core_term_type`, and `resolve_callee_function` in
   `elaborator/ElabTerm.thy`), but a statement-position impure call is
   accepted in ghost code and in a non-impure function, and
   `impure ghost function` is accepted. So the three rules have to be
   added:
   * the first and third belong in `well_ghosted` (and the elaborator);
   * the second is not a ghost rule. It belongs in Core's module
     typecheck, and it yields the lemma "calling a non-impure function
     leaves `IS_World` unchanged", which 6.4 relies on.

   The second rule is also missing today in a way that matters without
   this redesign: see the note in section 7.

   **Decided:** the three rules are added in a pass after the main
   work (stage 6). Until then the simulation proof uses `sorry` at the
   steps that rely on them. Those steps need two facts:
   * ghost code makes no call to an impure function;
   * the body of a non-impure function makes no call to an impure
     function.

   Once the rules are in place, the sorries are removed.
6. **Extern functions in a full run.** An extern has no body, so a
   ghost `ref` parameter of an extern has no value to be updated to.

   **Decided:** ghost parameters are forbidden on extern functions
   for now. The rule goes in `core_module_well_ghosted` (a function
   with `CF_Body = None` has no ghost parameter) and in the
   elaborator. This reverses the "Extern functions" paragraph of
   `GHOST_ARGS.md`, which allowed them because the C compiler does.
   The C is not changed: the C and the Isabelle deliberately differ on
   this point for now.
7. **Prove or check `well_ghosted`** in the elaborator (section 4).

   **Decided:** prove it, as well-typedness is proved today.
8. **Type soundness scope.** Extend it to all ghost constructs at
   once, or first restate it for executable programs only and extend
   later?

   **Decided:** restate it for all programs at once. The new cases are
   `sorry` at first; once the restated theorem builds, they are filled
   in (stage 3).
9. **`TE_RuntimeTypeVars` and `TE_GhostDatatypes`.** Typing will not
   read either. `TE_RuntimeTypeVars` is partly a declaration marker
   (an abstract type declared `type T` rather than `ghost type T`) and
   partly context (the type parameters of a non-ghost function). Do
   they stay in `CoreTyEnv` as inert fields, or move?

   **Decided:**
   * `TE_GhostDatatypes` stays a field of `CoreTyEnv`. Computing it
     instead was considered and dropped. "Ghost datatype" and "runtime
     type" are defined in terms of each other. Datatypes cannot be
     recursive, so the recursion does end, but nothing in the
     environment records that, and a computed version would need an
     acyclicity invariant for its termination proof. With the stored
     set, `is_runtime_type` is a plain structural function
     (`core/CoreTypeProps.thy:14`), and the elaborator fills the set
     in one datatype at a time, in declaration order
     (`elaborator/ElabDecl.thy:736`).
   * `TE_RuntimeTypeVars` is decided during implementation. Leaving it
     in `CoreTyEnv` as an inert field is acceptable if that is
     easiest.
   * Also for implementation: whether the two `tyenv_well_formed`
     conjuncts about `TE_GhostDatatypes`
     (`tyenv_ghost_datatypes_subset`,
     `tyenv_nonghost_payloads_runtime`) stay there or move to an
     environment invariant in `core_ghost`.

## 10. Suggested order

The uncertain part is the simulation proof, and it can be tried before
any refactoring, because today's Core already has the markers and
today's `NotGhost` typing already implies well-typed and
well-ghosted.

**Order of the remaining stages** (decided 3-Oct-2026): 5, 7, 6, 4.
The stages keep their numbers, because the rest of this document
refers to them by number. Stage 4 moves to the end for two reasons.

* Until stage 7, one-mode typing plus `well_ghosted` is proved
  equivalent to the old two-mode judgment, and the old judgment has no
  rules for ghost parameters. Doing stage 4 before stage 7 would mean
  either adding those rules to a judgment that is about to be deleted,
  or giving up the equivalence early.
* After stage 7 the elaborator proofs prove `well_ghosted` directly, so
  the changes of stage 4 are made once, in their final form.

The cost: stage 5 proves its `erase_ghost` lemmas for an `erase_ghost`
that does not yet drop ghost parameters. Stage 4 has to revisit the
call and function cases of those lemmas and of the simulation proof.

0. **(Done.)** Toy theory: a small interpreter with two-level fuel and
   one quantifier case. Confirms question 1.
1. **(Done; see section 11.)** In new files, starting from the
   committed state: the new
   interpreter (beside the old one in `interpreter/`), then
   `erase_ghost` and the simulation theorem (in `core_ghost/`), with
   today's `NotGhost` typing as the hypothesis. The steps that need
   the impure-call rules of question 5 are `sorry` until stage 6.
   `int`, `real` and `allocated` can be left out at this stage; they
   do not affect the shape of the proof. No existing file changes.
2. **(Done; see 11.4.)** Split typing into one-mode typing plus
   `well_ghosted`, as new definitions beside the old ones. Prove the
   old judgment equivalent to the pair. Restate the elaborator's
   top-level theorems over the new judgments, as corollaries of the
   equivalence. The old judgments stay until stage 7 (order revised
   2-Oct-2026: they cannot be deleted while type soundness,
   substitution, linking and match compilation are stated over them).
3. **(Done; see 11.5.)** Replace the old interpreter by the new one, with the constructor
   table in the state (question 2). Add `int` and `real` values.
   Restate type soundness for all programs, with `sorry` in the new
   cases; once that builds, fill them in (question 8). Type soundness
   and the simulation theorem are then stated over one-mode typing
   (and, for the simulation, `well_ghosted`), not the two-mode
   judgments.
4. **(Done last, after stage 6.)** Ghost parameters: `erase_ghost`
   drops them; the elaborator gets the end-of-statement rule from
   section 7, and rejects ghost parameters on extern functions
   (question 6). The `erase_ghost` lemmas of stage 5 and the simulation
   proof are updated for the dropped parameters and actuals.
5. **(Next.)** `well_ghosted` preservation and `erase_ghost`
   commutation for substitution, linking and match compilation.
6. **(After stage 7.)** Follow-up pass:
   * the three impure-call rules of question 5, which let the stage 1
     sorries be removed and close the gap noted in section 7;
   * run-time checking of loop invariants (question 4);
   * when Core gains `requires` and `ensures`, run-time checking of
     those too.
7. **(After stage 5.)** Remove the old judgments (added 2-Oct-2026). Rewrite the elaborator
   proofs to prove one-mode typing and `well_ghosted` directly, in
   place of the stage 2 corollaries. Move any remaining user of the
   two-mode judgments over. Then delete the two-mode judgments, the
   equivalence files, and `TE_GhostLocals` and `TE_FunctionGhost`, and
   drop the `2` from the new names. This needs stages 3 and 5 to be
   done; it does not depend on stage 6.

If stage 1 goes badly, nothing has been lost and `GHOST_ARGS.md` can be
resumed from the parked branch.

## 11. Progress

As of 3-Oct-2026: stages 0 to 3 are done, and stage 5 is next (the
remaining order is 5, 7, 6, 4; see section 10).
Everything listed as built has been checked by
Isabelle. Nothing is committed yet.

### 11.1 Stage 0: done

`isabelle/toy/TwoLevelFuel.thy` is a toy interpreter with two mutually
recursive functions, a loop-like construct and a quantifier over the
integers. It is not in `ROOT`; it is checked by opening it in the IDE.
It shows:

* the function package accepts the quantifier case, and termination is
  proved by the lexicographic order on `(d, fuel)`;
* monotonicity in fuel, where the quantifier case is trivial because
  its result does not mention the fuel;
* monotonicity in depth, where the quantifier case uses fuel
  monotonicity at both depths, and needs the "every instance defined
  first" rule of 3.5;
* determinism: any two runs that are not `InsufficientFuel` agree;
* `forall x. countdown(x) = 0` evaluates to true at depth 1 and any
  nonzero fuel.

### 11.2 Stage 1: files that exist

All nine are in `ROOT`, and all nine check in the IDE. The session
build fails on the one `sorry` in `GhostInvisible.thy` (see 11.3).

(The file and function names below are the ones used until sub-step 8
of stage 3. That sub-step moved the four `CoreInterp2*` files into
`CoreInterp.thy`, `CoreInterpFuelMono.thy`, `CoreInterpPreservation.thy`
and `CoreInterpFrame.thy`, and renamed `interp2_*` to `interp_*`; see
11.5. Sections 11.2 to 11.5 keep the old names where they describe
work done before that.)

| File | Contents |
|---|---|
| `interpreter/CoreInterp2.thy` | The new interpreter, beside the old one. |
| `interpreter/CoreInterp2FuelMono.thy` | Fuel monotonicity for it, at a fixed depth. |
| `interpreter/CoreInterp2Frame.thy` | The frame lemma (part 1 of the simulation proof). |
| `interpreter/CoreInterp2Preservation.thy` | Statements and calls do not change `IS_Globals`, `IS_Functions`, `IS_DefaultCtors` or (as seen by the caller) `IS_TyArgs`. |
| `core_ghost/EraseGhost.thy` | `erase_ghost_statement` and `erase_ghost_statement_list`. |
| `core_ghost/ErasedState.thy` | The state relation. |
| `core_ghost/GhostInvisible.thy` | Ghost statements are invisible (part 2 of the simulation proof). |
| `core_ghost/ErasedSteps.thy` | Steps that both states take together (helper lemmas for part 3). |
| `core_ghost/EraseGhostSimulation.thy` | The induction, and the simulation theorem (part 3). |

Choices made while writing them:

* **Names.** The new interpreter's functions are `interp2_term`,
  `interp2_statement` and so on. The names are temporary: stage 3
  renames them when the old interpreter is deleted. The file imports
  `CoreInterp.thy` and reuses its helper functions.
* **Quantifier and `Obtain`.** The `combine` of 3.5 is split into
  `instances_error` (the three-step error rule, shared), and
  `eval_quantifier` and `choose_witness` on top of it.
* **Domain of quantification.** `values_of_type` is declared with
  `consts` and left unspecified. Nothing in stage 1 needs to know what
  it is. Stage 3 defines it, once the state has a constructor table
  (question 2).
* **Left out of the new interpreter for now:** `int` and `real` values;
  `Allocated` (still a `TypeError`); loop-invariant checks (stage 6).
* **`assert *`** (no condition) is a `TypeError` at run time, like
  `Fix` and `Use`. The typing rule allows it only where there is a
  proof goal, and proof bodies are not run.
* **Equality** uses a small wrapper, `eval_binop2`, around the existing
  `eval_binop`.
* **`erase_ghost_statement` returns a statement list** (empty, or one
  statement). It looks only at the markers. The trivial `decreases`
  term is `CoreTm_LitBool False`. It does not yet drop ghost actuals
  (stage 4), and there is no module-level erasure yet.
* **The state relation** is `state_erased env emb full erased`. The
  address embedding of 6.3 is an explicit list `emb`: erased address
  `i` corresponds to full address `emb ! i`. It only has to be
  `distinct`; it does not have to be order-preserving. Running a
  statement extends it at the end (`emb @ extra`), and leaving a scope
  goes back to the earlier list.
* **The theorem** is `erase_ghost_simulation` in
  `EraseGhostSimulation.thy`: for a well-typed statement list of a
  non-ghost function, if the full run gives `Inr res` at `(d, fuel)`,
  the erased list gives some `Inr res'` at the same `(d, fuel)`, with
  the results related. (It was first stated with `oops` in
  `ErasedState.thy`; that statement has been removed.)

### 11.3 Stage 1: the simulation proof

The simulation proof, in three parts. All three are done
(2-Oct-2026). Two things are left open in it: the one `sorry` in part
2, and the hypothesis `fun_var_ref_agree` of the theorem.

(This section describes the proof as it was written in stage 1, over
the two-mode judgments. Sub-step 7 of stage 3 restated it; see 11.5
for what changed, including the removal of the `fun_var_ref_agree`
hypothesis.)

1. **Frame lemma. (Done, 2-Oct-2026.)** About the interpreter alone,
   with no typing. In `CoreInterp2Frame.thy`:
   * `interp2_function_call_frame`: a call returns the caller's
     `IS_Locals`, `IS_Refs`, `IS_ConstLocals` and `IS_TyArgs`
     unchanged, keeps the store at the same length, and leaves every
     cell outside `call_ref_addrs state fnName argTms` unchanged. That
     set is the addresses (`var_addr`) of the base variables of the
     argument terms in `Ref` parameter positions, so it does not
     mention the fuel.
   * `interp2_statement_frame` and `interp2_statement_list_frame`:
     running statements gives `frame_step state state'`. The store
     does not shrink, cells that the frame does not refer to
     (`frame_addrs`) are unchanged, and the new frame refers only to
     old frame addresses or newly allocated cells. `frame_step` is
     reflexive and transitive.
   * The proof is by induction on the fuel at a fixed depth, over the
     statement, statement-list and call functions only (terms return
     no state). It did not need the "every address is inside the
     store" invariant after all. That invariant is defined there as
     `addrs_in_bounds`, with preservation corollaries, for parts 2
     and 3 to use.
   * That `IS_Globals`, `IS_Functions` and `IS_DefaultCtors` are
     unchanged is in `CoreInterp2Preservation.thy`
     (`interp2_statement_static` and its two siblings), a port of
     `CoreInterpPreservation.thy` written for part 2.
2. **Ghost statements are invisible. (Done, 2-Oct-2026.)** In
   `GhostInvisible.thy`:
   * `ghost_statement_invisible` (and the `_list` version): a
     statement typed in `Ghost` mode, in a function that is not ghost,
     that runs to completion from `full`, gives `Continue full'` with
     `state_erased env' emb full' erased`: the same erased state and
     the same embedding. Writes go to ghost cells because of
     `ghost_lvalue_ok`; calls use the frame lemma.
   * `erased_statement_invisible`: the same for a statement typed in
     `NotGhost` mode with `erase_ghost_statement stmt = []`. This is
     the form part 3 uses. It rests on
     `erased_statement_ghost_typed`: such a statement has the same
     typing in `Ghost` mode.
   * The proof is by induction on the fuel at a fixed depth, over
     statements and statement lists only. Calls need no induction.
   * **One `sorry`**, in `ghost_call_invisible`: the fact "a ghost
     call leaves `IS_World` unchanged" (question 5). Stage 6 replaces
     it with a proof from the impure-call rules. Until then the
     session build fails (`ROOT` has no `quick_and_dirty`); the files
     are checked in the IDE.
   * A hypothesis, `fun_var_ref_agree`: the function table of
     the full state agrees with `TE_Functions` about which parameters
     are `Ref`. `funs_exist_in_state` gives this only for non-ghost
     functions, and ghost code may call ghost functions. Part 3 needs
     a function-table invariant for the full state that implies it.
3. **The main induction. (Done, 2-Oct-2026.)** On the fuel, with the depth fixed, mutually
   over the six interpreter functions. Executable code never reaches
   the `Quantifier` or `Obtain` cases, so the depth plays no part. A
   statement that erases to nothing is handled by part 2 and fuel
   monotonicity; a statement that erases to one statement runs in both
   states at the same fuel.
   * **Helper lemmas (done, 2-Oct-2026).**
     `ErasedSteps.thy` has one lemma for each kind of step that both
     states take: reading a variable, an lvalue that is a variable,
     declaring a variable in a new cell or as a ref, writing to a
     cell, swapping, leaving a scope, binding the arguments of a call,
     and the ref updates of an extern function. None of them needs an
     induction over the interpreter.
   * **The induction.** It is
     `erase_ghost_simulation_aux` in
     `core_ghost/EraseGhostSimulation.thy`. Fixed outside the
     induction: the depth, an environment `genv`, and the function
     table `funs` of the full state, with `fun_var_ref_agree
     (TE_Functions genv) funs` and `fun_bodies_typed genv funs` (the
     bodies of the non-ghost functions typecheck; it follows from
     `funs_exist_in_state`). Every statement has the premises
     `TE_Functions env = TE_Functions genv`, `IS_Functions full =
     funs` and `state_erased env emb full erased`. The six statements,
     each for a run in the full state that gives `Inr`:
     1. a term typed in `NotGhost` mode gives the same value in the
        erased state;
     2. the same for a list of such terms;
     3. an lvalue typed in `NotGhost` mode gives `(i, path)` in the
        erased state, where the full state gave `(emb ! i, path)`;
     4. a statement with `erase_ghost_statement stmt = [stmt']`:
        `stmt'` runs in the erased state, with a related result;
     5. a statement list: its erasure runs in the erased state, with
        a related result;
     6. a call of a non-ghost function with arguments typed in
        `NotGhost` mode: the same call runs in the erased state,
        returns the same value, and the states after it are related by
        the same embedding.
   * `tyenv_well_formed env` turned out not to be needed, and the
     theorem no longer assumes it. The theorem gains the hypothesis
     `fun_var_ref_agree` from part 2.
   * Lists of typed terms are stated with a definition, `terms_typed`,
     and not with `∀tm ∈ set tms`. The `rule_format` attribute turns a
     bounded quantifier into a meta-level rule even inside a premise,
     and the induction hypotheses are used through `rule_format`.

Module-level `erase_ghost`, `ghost_free` and theorem 4 are left until
`well_ghosted` exists (stage 2).

### 11.4 Stage 2: done

Stage 2 starts the same way as stage 1: new definitions beside the old
ones, in new files, with no existing file changed.

All three files are in `ROOT`, and all three check (2-Oct-2026).

| File | Contents |
|---|---|
| `core/CoreStmtTypecheck2.thy` | One-mode typing: `core_impure_call_type2`, `core_statement_type2`, `core_statement_list_type2`. |
| `core_ghost/WellGhosted.thy` | The ghost context, and `core_term_well_ghosted`, `core_statement_well_ghosted`, `core_statement_list_well_ghosted`. |
| `core_ghost/WellGhostedEquiv.thy` | The equivalence with the old judgments. |

Choices made:

* **One-mode term typing is `core_term_type env Ghost tm`.** Ghost
  mode has no ghost restrictions and never reads `TE_GhostLocals`, so
  no new term-typing function is needed yet. `core_term_type2 env tm`
  is an input abbreviation for it. Every existing lemma about
  `core_term_type` at a general mode is therefore already a lemma
  about one-mode typing. The same holds for `cast_result_type`.
* **One-mode statement typing is a new function.** The old Ghost mode
  requires every marker inside to be `Ghost`, so it cannot be reused.
  `core_statement_type2` does not read the markers, and does not read
  or update `TE_GhostLocals` and `TE_FunctionGhost`. The names end in
  `2` until the old functions are deleted.
* **The ghost context is a record, `GhostCtx`,** separate from
  `CoreTyEnv`: the ghost-local set (`GC_GhostLocals`) and the mode of
  the enclosing function (`GC_FunctionGhost`).
* **The well-ghosted definitions are predicates** (they return
  `bool`). They take the type environment of the program point, the
  ghost context and the mode. This settles the point left open in
  3.2: for the statements after a statement, the environment is the
  one `core_statement_type2` returns, and the ghost context is given
  by a small syntactic function, `gctx_after_statement`.
* **`core_term_well_ghosted` is `True` in `Ghost` mode.** All its
  content is in `NotGhost` mode. The statement version has content in
  both modes (a marker inside ghost code must be `Ghost`; ghost code
  writes only to ghost variables; ghost code does not return from a
  function that is not ghost).
* A variable is ghost if it is a local and is in `GC_GhostLocals`
  (`gctx_var_ghost`). The first condition copies `tyenv_var_ghost`, so
  that the equivalence below needs no invariant.

**The equivalence** (`WellGhostedEquiv.thy`, done 2-Oct-2026).
`tyenv_gctx env` is the ghost context read off an old-style
environment.

* `core_term_type_NotGhost_iff`: `core_term_type env NotGhost tm =
  Some ty` if and only if `core_term_type env Ghost tm = Some ty` and
  `core_term_well_ghosted env (tyenv_gctx env) NotGhost tm`.
* `core_statement_type_iff`: `core_statement_type env ghost stmt =
  Some env'` if and only if `core_statement_type2 env stmt` succeeds,
  `core_statement_well_ghosted env (tyenv_gctx env) ghost stmt` holds,
  and `env'` is the one-mode result with the ghost locals of
  `gctx_after_statement`.
* `core_statement_list_type_imp_split` and
  `split_imp_core_statement_list_type`: the two directions for
  statement lists.
* The working form is an equation, with the one-mode side stated for
  an environment whose `TE_GhostLocals` is overwritten by an arbitrary
  `g`: old typing = (if well-ghosted then one-mode typing else
  `None`). For terms this is `core_term_type_NotGhost_eq`; for
  statements, `core_statement_type_split`. The `g` is what lets the
  inductions go through binders and statement lists with no separate
  lemma that the new definitions ignore `TE_GhostLocals`.
* One fact about the old typing is proved first,
  `core_term_type_Ghost_cong_env` (moved to
  `core/CoreStmtTypecheck2Props.thy` in stage 3): in `Ghost` mode
  `core_term_type`
  does not depend on `TE_GhostLocals`, `TE_RuntimeTypeVars` or
  `TE_GhostDatatypes`. It will be the congruence lemma of one-mode
  typing.
* The statement proof is a structural induction on the statement (the
  first in this development; the datatype's induction rule gives a
  hypothesis for each statement of a nested list).

**Module level** (done 2-Oct-2026). Three more files, all in `ROOT`,
and all three check:

| File | Contents |
|---|---|
| `core/CoreModuleTypecheck2.thy` | `module_functions_well_typed2`, `normalized_module_well_typed2`, `core_module_well_typed2`: the module check with function bodies typed by `core_statement_list_type2`. |
| `core_ghost/WellGhostedModule.thy` | `module_body_gctx` (the ghost context at the start of a body), `module_functions_well_ghosted`, `normalized_module_well_ghosted`, `core_module_well_ghosted`. |
| `core_ghost/WellGhostedModuleEquiv.thy` | `core_module_well_typed_iff`: `core_module_well_typed m` if and only if `core_module_well_typed2 m` and `core_module_well_ghosted m`. |

Only the function-body clause is split. `tyenv_well_formed` and
`core_module_invariant` are used whole by `core_module_well_typed2`,
although seven clauses of the first are ghost rules
(`tyenv_vars_runtime`, `tyenv_ghost_vars_subset`,
`tyenv_return_type_runtime`, `tyenv_fun_ghost_constraint`,
`tyenv_nonghost_payloads_runtime`, `tyenv_ghost_datatypes_subset`,
`tyenv_runtime_tyvars_subset`), and `tyenv_module_scope` and
`module_ghost_subsets_ok` mention ghost fields. Splitting them is left
until it is known which of them the restated type soundness proof
needs (stage 3).

**The order of the rest** (agreed 2-Oct-2026; section 10 is updated
to match). The old judgments cannot be deleted at the end of stage 2.
The old interpreter's type soundness proof is stated over them, and so
are substitution, linking, match compilation and the stage 1 files.
The equivalence lets each of these move to the new judgments
separately, so the deletion comes last (stage 7).

**The elaborator's top-level theorems** (done 2-Oct-2026).
`elaborator/ElabProgramWellGhosted.thy`, in `ROOT`; it checks. For
the whole-program link and for the link of one module's
implementation, the result is `core_module_well_typed2` and
`core_module_well_ghosted`. These are theorems 1 and 2 of section 4,
as corollaries of `elab_program_well_typed`,
`module_impl_link_well_typed` and `core_module_well_typed_iff`. The
elaborator proofs themselves still prove the two-mode judgments
(stage 7 changes that).

**Next.** Stage 3. Restating the simulation theorem over one-mode
typing and well-ghosted is part of it: that needs `state_erased` and
the function-table hypotheses restated over the ghost context, which
is the same work as restating `state_matches_env`.

### 11.5 Stage 3: done

Done 3-Oct-2026: all nine sub-steps build. Type soundness has no
`sorry`. One `sorry` is left in the whole redesign, in
`core_ghost/GhostInvisible.thy` (a ghost call keeps `IS_World`); it
waits for the impure-call rules of stage 6. The next stage is 5.

Sub-steps agreed 2-Oct-2026. The old soundness files are edited in
place. Nothing is committed until the whole redesign is done; a backup
of the tree as it stood at the end of stage 2 exists outside the
repository.

**Progress.**

* Sub-step 1 (done 2-Oct-2026; the four files check). `value_has_type`
  no longer has the three runtime conditions. Changed files:
  `core/CoreValue.thy`,
  `core/CoreValueTransfer.thy`, `core/LinkPreservesWellTyped.thy`
  (one call site), `core_passes/MatchCompileSemantics.thy` (not
  edited; it uses `value_has_type`). `value_has_type_runtime` is
  deleted. Five lemmas lost hypotheses they no longer need:
  `value_has_type_cong_env` (the ghost-datatype and runtime-tyvar
  equalities), `value_has_type_cong_env_wk` (the ghost-datatype
  equality and the two runtime-type facts), `value_has_type_env_mono`
  and `value_has_type_tyenv_extends` (the ghost-marker clause and
  `tyenv_ctors_consistent`), `value_has_type_apply_subst_generic`
  (the ghost-datatype equality).
* The call sites in other files were updated in later sub-steps: four
  in `elaborator/ElabDeclCorrect.thy` (checked after sub-step 6), and
  those in `TypeSoundnessHelpers1` to `3` and `TypeSoundness.thy`
  (sub-steps 3 and 4).
* Sub-step 2 (done 2-Oct-2026; the five files check). It turned out to
  need a one-mode well-formedness predicate first (see "Well-formedness"
  below). Files:
  * `core/CoreTyEnvWellFormed2.thy` (new): `tyenv_well_formed2`, its
    link with `tyenv_well_formed`, and the lemmas for adding a local
    and for the fields it does not read.
  * `core/CoreValue.thy`: `value_has_type_well_kinded` and
    `value_has_type_cong_env_wk` now assume `tyenv_well_formed2`.
    Both are used only by the soundness files.
  * `core/CoreStmtTypecheck2Props.thy` (new): facts about one-mode
    typing. `core_term_type_Ghost_cong_env` moved here from
    `WellGhostedEquiv.thy`. New: `core_term_type_well_kinded2`,
    `core_impure_call_type2_fn_facts`,
    `core_statement_type2_fixed_eq` and
    `core_statement_type2_preserves_well_formed2`, with their list
    versions.
  * `core_ghost/WellGhostedEquiv.thy`: the moved lemma is removed and
    the new file imported.
  * `interpreter/StateMatchesEnv.thy`: the invariant for the new
    interpreter's state.
* What changed in the invariant (`StateMatchesEnv.thy`):
  * every local of the environment exists in the state, and every
    function, ghost or not;
  * `IS_ConstLocals state = TE_ConstLocals env`;
  * `IS_TyArgs` binds exactly `TE_TypeVars env`, to ground well-kinded
    types (no runtime condition);
  * a function body is typed by `core_statement_list_type2`;
  * `body_env_for` covers ghost functions (it sets `TE_GhostLocals`,
    `TE_RuntimeTypeVars` and `TE_FunctionGhost` as
    `module_body_env_for` does);
  * `body_env_for_well_formed` is about `tyenv_well_formed2`, for any
    function;
  * `extern_fun_contract` no longer assumes the type arguments are
    runtime types. This makes the contract stronger: ghost code may
    call an extern function at any ground, well-kinded type arguments,
    and one-mode typing does not rule that out.
* Sub-step 3, `TypeSoundnessHelpers1.thy` and `TypeSoundnessHelpers2.thy`
  (done 2-Oct-2026; both check). What changed:
  * `sound_statement_result` asks for `tyenv_well_formed2` of the
    middle environment.
  * New lemma `value_has_type_ground_cong_env` (in `Helpers1`):
    `value_has_type` is the same in two environments that agree on
    `TE_DataCtors` and `TE_Datatypes`. It needs nothing about
    `TE_TypeVars`, because `value_has_type` only mentions ground types.
    It replaces every use of `value_has_type_cong_env_wk`, and removes
    about 700 lines of transfer between the caller's and the callee's
    environment from `Helpers2`. With it come
    `extern_fun_contract_ground_cong_env` and
    `fun_info_matches_interp_fun_ground_cong_env`. At cleanup the lemma
    should move to `core/CoreValue.thy` and
    `value_has_type_cong_env_wk` should be deleted. (It is in `Helpers1`
    for now so that `CoreValue.thy` and everything above it need not be
    checked again.)
  * New lemma `state_matches_env_cong_env` (in `Helpers1`): the
    invariant does not read `TE_GhostLocals`, `TE_ReturnType`,
    `TE_FunctionGhost`, `TE_ProofGoal` or `TE_ProofTopLevel`. This is
    for the `Let` case, whose typing rule (in Ghost mode) adds the
    variable to `TE_GhostLocals`.
  * The lemmas that add a local or a reference
    (`state_matches_env_add_local`, `_add_const_local`,
    `_add_nonconst_local`, `_add_ref`) take an environment update with
    no `TE_GhostLocals` part, as `core_statement_type2` produces.
    `_add_ref` lost its two freshness hypotheses (they were not needed).
    `state_matches_env_add_ghost_local` is deleted: a ghost declaration
    is now executed like any other.
  * `is_runtime_type_apply_IS_TyArgs` is deleted (it is false now).
    `is_runtime_type_apply_IS_TyArgs_ground` is replaced by
    `is_well_kinded_apply_IS_TyArgs_ground`.
    `is_well_kinded_apply_IS_TyArgs` lost its unused well-formedness
    hypothesis.
  * `make_1d_array_typed` lost its runtime-type hypothesis.
  * New lemma `fun_info_types_tyvars_subset` (in `Helpers2`): the types
    in a function's signature mention only the function's own type
    variables. It holds for ghost functions too, and replaces the uses
    of `tyenv_fun_ghost_constraint` for this purpose.
  * `partial_body_env_for_well_formed`,
    `cleared_state_matches_partial_env_zero`,
    `process_one_arg_step_sound`, `fold_process_one_arg_sound_gen` and
    `fold_process_one_arg_sound` lost the "function is not ghost" and
    "type arguments are runtime types" hypotheses.
    `cleared_state_matches_partial_env_zero` now needs only the
    invariant and the facts about the type arguments.
    `fold_process_one_arg_sound` is stated for `interp2_term` and
    `interp2_writable_lvalue`.
  * `restore_scope_sound` lost three hypotheses (the ghost-datatype
    equality and the two well-formedness facts).
* Sub-step 3, `TypeSoundnessHelpers3.thy` (done 2-Oct-2026; it checked,
  and then got one small change in sub-step 4, see there). Every lemma
  is restated for Ghost-mode typing,
  `tyenv_well_formed2` and `interp2_*` (with the depth `d` as an extra
  free variable; the induction hypotheses are at the same depth).
  What changed beyond that:
  * Two `sorry`s, both waiting for `int` and `real` values (sub-step 9):
    in `type_soundness_cast`, the case where the cast target is `int`
    and `cast_value` fails; in `type_soundness_default`, the case where
    the type (after substitution) is not a runtime type.
    `default_value_sound` itself is unchanged and still asks for a
    runtime type.
  * `value_has_type_not_math` (new, temporary): no value has type `int`
    or `real`. It replaces `value_has_type_runtime` where that was used
    to rule those two types out. It becomes false in sub-step 9, and
    the proofs that use it (`eval_unop_sound`, `eval_binop_sound`) then
    need the new cases.
  * `eval_unop_sound` and `eval_binop_sound` take the typing mode as a
    variable. `eval_binop_sound` has a new last hypothesis: for an
    equality, the operand type is `bool` or numeric. (In Ghost mode the
    typing rule allows equality at any type, and `eval_binop` does not
    handle that.) `ConstFoldCorrect.thy` must supply it; it follows
    from `binop_operand_type_bool_or_numeric`.
  * `eval_binop2_sound` (new): the interpreter's `eval_binop2`. Equality
    and inequality need nothing about the operand values.
  * `unop_operand_apply_subst_any` and `binop_operand_apply_subst_ne`
    (new): versions of two lemmas of `core/TypeSubstTerm.thy` that hold
    in either mode. The originals are stated for `NotGhost` only; they
    were not changed, to avoid re-checking the files above
    `TypeSubstTerm.thy`.
  * `cast_value_error_is_runtime` asks for "the target is not `int`"
    instead of "the target is a runtime type".
    `apply_cast_opt_error_is_runtime` takes any typing mode and has a
    new hypothesis "the result type is not `int`".
  * `type_soundness_function_call` lost the "not ghost" and "type
    arguments are runtime types" hypotheses. Its statement-list
    induction hypothesis is over `core_statement_list_type2`.
* Sub-step 4, `TypeSoundness.thy` (done 2-Oct-2026; it checks, and so
  does `Helpers3` after its change).
  * **No proof goal.** `Fix`, `Use` and `assert *` are typeable where
    there is a proof goal, and the interpreter cannot run them. They
    only occur in the proof body of an `Assert`, which is not run. So
    the two statement conclusions of the theorem have the extra
    hypothesis `TE_ProofGoal env = None`. It is kept through a
    statement list by the new lemma `core_statement_type2_no_goal`
    (in `TypeSoundness.thy` for now; it belongs in
    `core/CoreStmtTypecheck2Props.thy`). A function body is typed with
    no proof goal (`body_env_for` sets it to `None`), so the
    function-call conclusion needs no such hypothesis. For this, the
    statement-list induction hypothesis of
    `type_soundness_function_call` in `Helpers3` got the premise
    `TE_ProofGoal env0 = None`.
  * **Structure.** `type_soundness_at_depth` is the old proof (induction
    on the fuel) at a fixed depth `d`, with the hypothesis that terms
    are sound at every smaller depth. `interp2_term_sound_all_depths`
    discharges that hypothesis by induction on the depth.
    `type_soundness` is the theorem at every depth and fuel; its six
    conclusions keep their names (`interp_term_sound` and so on).
  * **Five `sorry`s:** `Quantifier` and `Obtain` at a positive depth
    (they need `values_of_type`); `Allocated`; a failed cast to `int`
    in `VarDeclCall` and in `AssignCall`.
  * **New cases proved:** `Old` (the identity) and `Assert` with a
    condition (evaluates it; `RuntimeError` if false).
  * Ghost branches are gone: a ghost declaration, assignment, swap,
    loop or match is run like any other. The inline proof for a
    reference declaration is replaced by `state_matches_env_add_ref`.
* Sub-step 5 (done 2-Oct-2026; the three files check).
  * `interpreter/MakeInterpState.thy`: `build_interp_funs` no longer
    skips ghost functions. A ghost function with no body is treated
    like any extern function: it needs a supplied `ExternFunc`.
  * `interpreter/MakeInterpStateCorrect.thy`: the hypothesis of
    `make_interp_state_matches_env` is `core_module_well_typed2`
    (weaker than before). `build_interp_funs_lookup_none` now says
    that a name not in the list is not in the map.
    `assembled_state_matches` lost two hypotheses it does not need
    (`tyenv_well_formed`, and `TE_RuntimeTypeVars env = {||}`). New
    lemma `core_module_well_typed2_env_well_formed2`: the normalized
    environment of a well-typed module satisfies `tyenv_well_formed2`.
  * `elaborator/EndToEnd.thy`: it imports `ElabProgramWellGhosted` and
    uses `elab_program_well_typed2`. New theorem
    `compile_program_env_well_formed` gives the second hypothesis of
    `type_soundness`.
* Sub-step 6 (done 2-Oct-2026; `ConstFoldCorrect.thy` checks).
  * `core_passes/MatchCompileSemantics.thy` needs no change: it does
    not use the interpreter (it has its own walker and `matches`).
  * `elaborator/ConstFoldCorrect.thy`, type preservation: two call
    sites updated (`make_1d_array_typed`, `eval_binop_sound`). The
    typing hypothesis is still `NotGhost` mode, which is what the
    elaborator has until stage 7.
  * `elaborator/ConstFoldCorrect.thy`, agreement with the interpreter:
    restated for `interp2_term d`, at any depth `d`. **The agreement
    theorems have a new hypothesis, `eval_const vals tm ≠ Inl
    TypeError`.** The new interpreter accepts two things that
    `eval_const` rejects with `TypeError`: equality at a value that is
    not a bool or a finite integer (`eval_binop2` against
    `eval_binop`), and `CoreTm_Old` (the identity against
    `TypeError`). So the unconditional equation is false. With the
    hypothesis, the interpreter returns what `eval_const` returns:
    a value, or `RuntimeError`. `fold_const_interp_agree` and
    `fold_const_is_core_evaluation` are about a successful fold and
    keep their statements. New lemma `eval_binop2_eq_eval_binop`.
  * **Decided (2-Oct-2026): the hypothesis stays.** `eval_const` only
    has to work on terms that are not ghost, so it is not changed to
    follow the interpreter. (The alternative was to give it
    `eval_binop2` and `Old` as the identity; that would have changed
    `ConstFold.thy`, which is in the exported compiler.) So
    `eval_binop` (bools and finite integers, used by `eval_const`) and
    `eval_binop2` (equality at any type, used by the interpreter) both
    stay.
* Checked after sub-steps 5 and 6 (2-Oct-2026), all with no errors:
  `MakeInterpState.thy`, `MakeInterpStateCorrect.thy`,
  `ConstFoldCorrect.thy`, `ElabDeclCorrect.thy` (four call sites
  changed in sub-step 1), `ElabModuleCorrect.thy`,
  `ElabProgramCorrect.thy`, `ElabProgramWellGhosted.thy`,
  `EndToEnd.thy`. So everything from the old soundness proof up to the
  end-to-end theorem is now stated for the new interpreter and checks.
  The four simulation files in `core_ghost` have not been checked
  since stage 3 began, and are expected to be broken by the new
  invariant until sub-step 7.
* Sub-step 7 (done 2-Oct-2026; the five files check). The four
  simulation files are restated over one-mode typing, the well-ghosted
  predicates and the new invariant. No two-mode judgment is left in
  them. Files: `WellGhosted.thy` (one definition added),
  `ErasedState.thy`, `GhostInvisible.thy`, `ErasedSteps.thy`,
  `EraseGhostSimulation.thy`.
  * **The ghost context is a parameter of the state relation.**
    `state_erased env gctx emb full erased` and `result_erased env gctx
    emb res res'`. A local is ghost if `gctx_var_ghost env gctx name`
    (before: `tyenv_var_ghost env name`, which read `TE_GhostLocals`).
    The relation reads the environment only through `TE_LocalVars` and
    `TE_Functions`.
  * **`gctx_after_statements`** (new, in `WellGhosted.thy`): the ghost
    context after a statement list. The conclusions about a statement
    or a list are stated in the environment that typing returns and
    the ghost context that `gctx_after_statement(s)` gives.
  * **Terms need no typing hypothesis.** The three statements of the
    induction about terms, term lists and lvalues assume only
    `core_term_well_ghosted env gctx NotGhost tm`. Every fact the old
    proof took from `NotGhost` typing (the variable is not ghost, the
    callee is not ghost, there is no quantifier, `allocated` or `old`)
    is a clause of that predicate. The `terms_typed` definition is
    gone; a list of terms is `list_all (core_term_well_ghosted env gctx
    NotGhost) tms`.
  * **Statements take both.** `core_statement_type2 env stmt = Some
    env'` and `core_statement_well_ghosted env gctx NotGhost stmt`.
    Typing is needed for the environment of the statements that
    follow. "The function is not ghost" is `GC_FunctionGhost gctx =
    NotGhost`.
  * **Ghost statements are invisible** (`GhostInvisible.thy`): for a
    statement with `core_statement_type2` and
    `core_statement_well_ghosted env gctx Ghost stmt`.
    `erased_statement_ghost_typed` is replaced by
    `erased_statement_ghost_mode`: a statement that erases to nothing
    and is well-ghosted in `NotGhost` mode is well-ghosted in `Ghost`
    mode. `ghost_call_invisible` takes
    `core_impure_call_well_ghosted` and no typing.
  * **`fun_var_ref_agree` is no longer a hypothesis of the theorem.**
    It follows from `funs_exist_in_state`, which now covers every
    function (`funs_exist_in_state_var_ref_agree`).
  * **New hypothesis: `funs_well_ghosted env (IS_Functions full)`**
    (defined in `ErasedSteps.thy`): the body of every function in the
    state is well-ghosted, in `body_env_for`, the ghost context
    `module_body_gctx` and the mode `FI_Ghost`. The state invariant is
    about typing only, so it cannot give this. It is what
    `module_functions_well_ghosted` says of a module. **Left open:** the
    lemma that `make_interp_state` of a well-ghosted module gives it
    (the counterpart of `make_interp_state_matches_env`).
  * **The theorem** (`erase_ghost_simulation`): hypotheses
    `GC_FunctionGhost gctx = NotGhost`, `funs_exist_in_state full env`,
    `funs_well_ghosted env (IS_Functions full)`, `state_erased env gctx
    emb full erased`, `core_statement_list_type2 env stmts = Some env'`,
    `core_statement_list_well_ghosted env gctx NotGhost stmts`, and the
    run of the full state. Conclusion: the erased list runs, with
    `result_erased env' (gctx_after_statements gctx stmts) emb res
    res'`. `erase_ghost_simulation_state_matches` is the same with
    `state_matches_env full env storeTyping` in place of
    `funs_exist_in_state`.
  * The one `sorry` (ghost calls keep `IS_World`) is unchanged.
* Sub-step 8 (done 2-Oct-2026; all the files check). The old interpreter
  is deleted, and the new one has its names. No proof was changed: the
  work is deletion, moving text between files, and renaming.
  * **Names.** `interp2_*` is `interp_*` everywhere (the six functions
    and every lemma name). `process_one_arg_more_fuel2` and
    `fold_process_one_arg_more_fuel2` lost the `2`.
  * **Files.** The four `CoreInterp2*` files are gone. Their content is
    in the old file names, so that the diff of each old file against
    the last commit shows how the interpreter and its proofs changed:
    * `interpreter/CoreInterp.thy`: the helper functions as before,
      then the content of `CoreInterp2.thy` in place of the old
      interpreter.
    * `interpreter/CoreInterpFuelMono.thy`: the old helper lemmas about
      `process_one_arg` and `default_value`, then the content of
      `CoreInterp2FuelMono.thy`. The old `process_one_arg_more_fuel`,
      `fold_process_one_arg_more_fuel` and `interp_fuel_mono` are
      deleted.
    * `interpreter/CoreInterpPreservation.thy`: the old helper lemmas
      (`..._preserves_globals_funs`), then the content of
      `CoreInterp2Preservation.thy`. The old main lemma, its
      corollaries and `exec_result_preserves_gf` are deleted; nothing
      used them. `result_state` is defined here now.
    * `interpreter/CoreInterpFrame.thy`: `CoreInterp2Frame.thy` under
      its new name. It imports `CoreInterpPreservation`. (Before, the
      preservation file imported the frame file, and only for
      `result_state`.)
  * **Imports.** `TypeSoundnessHelpers1` imports
    `CoreInterpPreservation`; `ErasedState` imports `CoreInterp`;
    `GhostInvisible` imports `CoreInterpFrame`; `EraseGhostSimulation`
    imports `CoreInterpFuelMono`. `ROOT` lists the four files.
  * **Renamed only** (no other change): `TypeSoundness.thy`,
    `TypeSoundnessHelpers2.thy`, `TypeSoundnessHelpers3.thy`,
    `elaborator/ConstFoldCorrect.thy`, and `ErasedSteps.thy`,
    `GhostInvisible.thy`, `EraseGhostSimulation.thy` in `core_ghost`.
  * **Check order:** `CoreInterp`, `CoreInterpFuelMono`,
    `CoreInterpPreservation`, `CoreInterpFrame`,
    `TypeSoundnessHelpers1` to `3`, `TypeSoundness`,
    `MakeInterpStateCorrect`, `ConstFoldCorrect`, `EndToEnd`, then
    `ErasedState`, `GhostInvisible`, `ErasedSteps`,
    `EraseGhostSimulation`.
  * **After the check:** with the decision under sub-step 6, the
    comments in `elaborator/ConstFold.thy` about agreement with
    `interp_term` were reworded (four places; comments only, not
    checked again). They now say that the two agree on a constant term
    whenever `eval_const` does not return `TypeError`.
  * `eval_binop2` keeps its name for now. It is no longer a temporary
    copy: both functions stay, so the `2` cannot simply be dropped.
  * **Changed 5-Oct-2026 (builds): `eval_binop2` is merged into
    `eval_binop`.** Equality and inequality in `eval_binop` now compare
    any two values, and `eval_const` uses the same function as the
    interpreter. `eval_binop2`, `eval_binop2_sound` and
    `eval_binop2_eq_eval_binop` are deleted; `eval_binop_sound` loses
    its equality hypothesis and asks for the operand values to be typed
    only when the operator is not an equality.
  * **Changed 5-Oct-2026 (builds): the `eval_const vals tm ≠ Inl
    TypeError` hypothesis is gone.** `is_constant_term` is now false on
    `CoreTm_Allocated` and `CoreTm_Old` (they have no type in a term
    that is not ghost), so the agreement theorems in
    `ConstFoldCorrect.thy` are unconditional again, and `agree_list`
    and the `Binop` and `ArrayProj` cases are back to their simpler
    proofs. This reverses the decision of 2-Oct-2026 above.
* Sub-step 9 (done 3-Oct-2026; the whole session builds). Done in three
  parts.
  * **Part 1, `int` and `real` values (done 3-Oct-2026; the whole
    session builds, including the code export).**
    * `core/CoreValue.thy`: constructors `CV_Int int` and `CV_Real
      real` (the theory now imports `HOL.Real`). `value_has_type` gives
      them the types `int` and `real`. New lemmas
      `value_has_type_MathInt` and `value_has_type_MathReal`. Every
      induction on a value has the two new cases, here and in
      `CoreValueTransfer.thy`.
    * `interpreter/CoreInterp.thy`:
      * `is_zero` and `eval_unop` (negation) cover the new values.
      * New helpers `generic_integer_binop`, `generic_numeric_binop`
        and `generic_numeric_cmp_binop`: they handle `int` and `real`
        operands and fall back to `generic_int_binop` and
        `generic_int_cmp_binop`. `eval_binop` uses them for `+ - * /`,
        modulo and the four orderings. Bitwise operators and shifts
        still take finite integers only. Equality in `eval_binop` also
        compares two `int`s or two `real`s.
      * `cast_value` casts between `int` and the finite integer types
        (to `int` always succeeds; to a finite type checks the range).
      * `default_value` is zero at `int` and `real`.
      * These helpers are shared with `eval_const`, so they are part of
        the exported compiler. `eval_const` is only run on constants
        that are not ghost, so it never meets the new values. The
        export accepts `real`.
      * `cast_value` has a "anything else is a `TypeError`" clause for
        each target type, ahead of the final catch-all. With the
        catch-all alone, the function package generated one equation
        twice and the simplifier warned about a duplicate rule.
    * `TypeSoundnessHelpers3.thy`: both `sorry`s are gone.
      `value_has_type_not_math` is deleted. `cast_value_error_is_runtime`
      and `apply_cast_opt_error_is_runtime` lost the "target is not
      `int`" hypothesis. `eval_binop_sound` is now proved from two new
      lemmas, `eval_binop_sound_math` (operands of type `int` or
      `real`) and `eval_binop_sound_finite` (the old proof).
      `default_value_sound` no longer asks for a runtime type.
    * `TypeSoundness.thy`: the two cast `sorry`s (`VarDeclCall`,
      `AssignCall`) are gone. Three are left: `Quantifier`, `Obtain`,
      `Allocated`.
    * The two new cases were also added to the proofs that list the
      value constructors by name: `CoreInterpFuelMono.thy`,
      `CoreInterpPreservation.thy`, `CoreInterpFrame.thy`,
      `TypeSoundnessHelpers1.thy`, `core_ghost/GhostInvisible.thy`,
      `core_ghost/EraseGhostSimulation.thy`. One step in
      `core_passes/MatchCompileSemantics.thy` (an integer column's
      value is a finite integer) now uses the pattern's compatibility
      with the column type; "the column type is an integer type" is no
      longer enough.
  * **Part 2, the quantifier's domain (done 3-Oct-2026, builds).**
    * `InterpState.thy`: two new fields, `IS_Datatypes` and
      `IS_DataCtors`, with the types of `TE_Datatypes` and
      `TE_DataCtors`.
    * `CoreInterp.thy`: `values_of_type` is now a definition: the
      values that have the type in any environment whose two tables are
      the state's. No environment is built from the tables;
      `value_has_type` on a ground type reads nothing else
      (`value_has_type_ground_cong_env`), so the set is the same for
      every such environment.
    * `StateMatchesEnv.thy`: `tables_match` (the state's two tables
      equal the environment's), a new conjunct of `state_matches_env`,
      placed after `default_ctors_match`.
    * The new conjunct is proved wherever `state_matches_env` is put
      together: three lemmas in `TypeSoundnessHelpers1.thy`, two in
      `TypeSoundnessHelpers2.thy`, and `MakeInterpStateCorrect.thy`.
      `restore_scope_sound` needs no new hypothesis: the tables of the
      restored state are those of the state after the call, which
      match `env_mid`, and `env_mid` has `env`'s tables.
    * `static_parts_eq` and the preservation lemmas are unchanged, and
      so are the `core_ghost` files: erased code has no quantifier and
      no `Obtain`, so the simulation never reads the tables.
    * `base_interp_state` fills the tables from the environment.
      `const_eval_state` (`ConstFoldCorrect.thy`) has them empty.
    * `TypeSoundnessHelpers3.thy`, new at the end: `values_of_type_iff`,
      `converged_cases`, `eval_quantifier_sound`,
      `choose_witness_sound`, `bind_local_sound`,
      `type_soundness_quantifier`, `type_soundness_obtain`.
    * `TypeSoundness.thy`: the `Quantifier` and `Obtain` `sorry`s are
      replaced by calls to the last two. One `sorry` is left,
      `Allocated`.
  * **Part 3, `Allocated` (done 3-Oct-2026, builds).**
    `allocated` cannot be a function on the value alone: a fixed-size
    array and an allocatable array can have the same value, and only
    the second is allocated. The interpreter does not have the
    operand's type. Decided 3-Oct-2026: for now `CoreTm_Allocated`
    always gives `false` and does not evaluate its operand. Giving the
    term a type annotation, and the interpreter the real definition, is
    a separate piece of work outside this plan.
    * `CoreInterp.thy`: the clause gives `CV_Bool False`.
    * `TypeSoundness.thy`: the last `sorry` is gone.
    * `ConstFoldCorrect.thy`: in the agreement proof, the `Allocated`
      case now uses the hypothesis that `eval_const` does not give
      `TypeError`, as the `Old` case does.

**Well-formedness** (found 2-Oct-2026). One-mode typing does not
preserve `tyenv_well_formed`. It does not track `TE_GhostLocals`, so
after declaring a local whose type is not a runtime type, the clause
"locals that are not ghost have runtime types" fails. So the soundness
proof cannot keep `tyenv_well_formed` as its hypothesis.
`tyenv_well_formed2` is `tyenv_well_formed` without the four clauses
that depend on which locals are ghost or on the mode of the enclosing
function (`tyenv_ghost_vars_subset`, `tyenv_return_type_runtime`,
`tyenv_return_type_complete`, and the locals half of
`tyenv_vars_runtime`). One-mode typing preserves it, and
`tyenv_well_formed` implies it. It still has the ghost clauses about
the parts of the environment that statements never change (functions,
datatypes, type variables, globals); those move to the well-ghosted
side in stage 7.

It equals `tyenv_well_formed` of the environment in which every local
is ghost and the function is ghost (`tyenv_all_ghost`). That is how
lemmas about `tyenv_well_formed` are reused: a one-mode version is the
old lemma applied at that environment.

Rule followed for lemmas that take `tyenv_well_formed`: one used only
by the soundness files is restated in place over `tyenv_well_formed2`;
one used elsewhere keeps its statement and gets a variant whose name
ends in `2`.

**What exists.** The old soundness proof is about 12,600 lines:
`StateMatchesEnv.thy` (715), `TypeSoundnessHelpers1` to `3` (8,669),
`TypeSoundness.thy` (2,966), and `MakeInterpState.thy` with its
correctness proof (656). Three files above it use the old interpreter:
`elaborator/ConstFoldCorrect.thy` (the constant evaluator agrees with
`interp_term`), `core_passes/MatchCompileSemantics.thy`, and
`elaborator/EndToEnd.thy`. The exported compiler does not contain the
interpreter, but it does contain `CoreValue` and the helper functions
of `CoreInterp.thy` (`eval_binop`, `cast_value`), through
`ConstFold.thy`.

**What has to change.**

* `value_has_type` (`core/CoreValue.thy`) requires the type arguments
  of a datatype and the element type of an array to be runtime types,
  and rejects values of ghost datatypes. Ghost values now exist, so
  these three conditions go (question 2 already says so).
* `state_matches_env` describes the old interpreter's state: only the
  locals that are not ghost exist, only the functions that are not
  ghost exist, `IS_ConstLocals` leaves out the ghost names, and
  `IS_TyArgs` binds the runtime type variables only. In the new
  interpreter's state all locals and all functions exist, and
  `IS_TyArgs` binds every type variable of the function.
* The body of a function in the state is typed by one-mode typing
  (`fun_info_matches_interp_fun` hard-wires `NotGhost` today).
* The theorem is stated for `interp2_*`, at every depth and fuel, with
  one-mode typing as the hypothesis. The proof becomes an induction on
  the depth around the existing induction on the fuel.

**Sub-steps.** Each is one file, or a few small ones, checked before
the next.

1. `value_has_type` without the runtime conditions. Fix
   `CoreValue.thy` and `CoreValueTransfer.thy`. The lemma
   `value_has_type_runtime` (a value's type is a runtime type) becomes
   false and is deleted; it has 13 uses, all in
   `TypeSoundnessHelpers2` and `3`.
2. The state invariant: `state_matches_env` for the new interpreter's
   state, and `body_env_for` for ghost functions too
   (`module_body_env_for` already covers them).
3. `TypeSoundnessHelpers1`, `2`, `3`: the result predicates and the
   helper lemmas, over the new invariant and `interp2_*`.
4. `TypeSoundness.thy`: the theorem. `Quantifier`, `Obtain`,
   `Allocated`, and anything of type `int` or `real` are `sorry` at
   first (question 8).
5. `make_interp_state` puts the ghost functions in the state;
   `MakeInterpStateCorrect.thy` and `EndToEnd.thy` follow.
6. `ConstFoldCorrect.thy` and `MatchCompileSemantics.thy` restated for
   `interp2_*`.
7. The simulation theorem and the other `core_ghost` files, with
   one-mode typing, `well_ghosted` and the new invariant as
   hypotheses. The `fun_var_ref_agree` hypothesis should then follow
   from the invariant, since the state now has every function.
8. Delete the old `interp_*` functions and their two proof files
   (`CoreInterpFuelMono.thy`, `CoreInterpPreservation.thy`); rename
   `interp2_*` to `interp_*`.
9. The new cases: `int` and `real` values, the constructor table in
   the state and the definition of `values_of_type`, `Allocated`.
   Then fill in the `sorry`s of sub-step 4.

**Decisions.**

* **In place** (decided 2-Oct-2026). Stages 1 and 2 put new files
  beside the old ones. Stage 3 edits the old files in place, from the
  bottom up. The new proof is the old one with changes, and
  `value_has_type` is shared by both, so a copy would need its own
  `value_has_type2` and about 14,000 duplicated lines that are deleted
  at the end. The cost is that the files above the one being edited do
  not check until their turn comes (the three files named above, and
  the `core_ghost` files).

* **`tyenv_well_formed`** (settled by necessity, 2-Oct-2026). The
  soundness proof takes `tyenv_well_formed2`; see "Well-formedness"
  above. The earlier proposal, to keep `tyenv_well_formed` whole as the
  hypothesis during the port, does not work.

The remaining two were proposals; both were confirmed on 3-Oct-2026.

* **What the state carries for the quantifier's domain** (question 2).
  Proposal: two tables, the datatype arities and the constructors.
  Without the runtime conditions `value_has_type` reads only
  `TE_Datatypes` and `TE_DataCtors` on ground types, so
  `values_of_type` can be `value_has_type` in an environment built
  from the two tables, and the invariant says the tables equal the
  environment's. This is only needed in sub-step 9.
* **When `int` and `real` values are added.** Proposal: last
  (sub-step 9). A new `CoreValue` constructor breaks every proof that
  splits on the value, so it is better done once the port checks.
  `CV_Real` also reaches the exported compiler through `ConstFold`,
  which needs a look at that point.

### 11.6 Things learned

* `dom` is a constant (`Map.dom`), so it cannot be used as a variable
  name in a definition.
* A premise of the form `∀m m'. ... ⟶ f m' = f m` makes `simp` loop.
  Use `unfolding ... by blast`.
* In the induction rule of a `function` definition, the variables of
  each case are the pattern variables of that equation in order,
  wildcards included. Counting them from the definition was enough to
  write all 51 cases of `CoreInterp2FuelMono.thy` without seeing the
  rule.
* `simp` does not reorder record updates by default: `f (r⦇a := x,
  b := y⦈)` and `f (r⦇b := y, a := x⦈)` stay different terms. The
  option `record_sort_updates` makes it put them in a fixed order
  (`declare [[record_sort_updates]]`, or `supply` it in one proof).
* `thm[OF a b]`, where `b` is itself a rule with a premise, does not
  discharge that premise: it stays behind as an extra subgoal, ahead
  of the premises not yet supplied. A following `simp` then works only
  on that subgoal. Use `simp_all`.
* `auto` does not use a fact `Some x = t` (constructor on the left) to
  prove `∃y. t = Some y` or `t ≠ None`. State the intermediate fact as
  `t = Some x`.
* `simp` does not rewrite inside the branches of a `case` on an option
  or a sum (the weak congruence rule stops it), but it does inside a
  `case` on a pair. `unfolding` with the same equations rewrites
  everywhere.

## 12. References

1. J.-C. Filliâtre, L. Gondelman, A. Paskevich. "The Spirit of Ghost
   Code". CAV 2014. The same erasure theorem, with the same
   termination requirement. Ghost-ness is in the type system and
   erasure is a function.
2. S. Owens, M. Myreen, R. Kumar, Y. K. Tan. "Functional Big-Step
   Semantics". ESOP 2016. The case for clocked (fuel-based)
   interpreters over relational big-step.
