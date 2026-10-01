# Proposal: ghost code by erasure

Status: proposal for discussion (1-Oct-2026). Nothing described here is
implemented. If adopted, it replaces section 3 of `GHOST_ARGS.md` (see
section 7 below).

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
| `allocated` | a function on the value, following `docs/lang-ref.md` |
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

**(unverified)** I believe the function package accepts the recursive
calls under `λm` and `λv` without a congruence rule, because the
termination condition needs no context beyond `d < Suc d`. A toy
theory should confirm this before anything else is built.

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

0. Toy theory: a small interpreter with two-level fuel and one
   quantifier case. Confirms question 1.
1. In new files, starting from the committed state: the new
   interpreter (beside the old one in `interpreter/`), then
   `erase_ghost` and the simulation theorem (in `core_ghost/`), with
   today's `NotGhost` typing as the hypothesis. The steps that need
   the impure-call rules of question 5 are `sorry` until stage 6.
   `int`, `real` and `allocated` can be left out at this stage; they
   do not affect the shape of the proof. No existing file changes.
2. Split typing into one-mode typing plus `well_ghosted`. Before deleting
   the old judgment, prove it equivalent to the pair. Retarget the
   elaborator proofs.
3. Replace the old interpreter by the new one, with the constructor
   table in the state (question 2). Add `int` and `real` values.
   Restate type soundness for all programs, with `sorry` in the new
   cases; once that builds, fill them in (question 8).
4. Ghost parameters: `erase_ghost` drops them; the elaborator gets the
   end-of-statement rule from section 7, and rejects ghost parameters
   on extern functions (question 6).
5. `well_ghosted` preservation and `erase_ghost` commutation for
   substitution, linking and match compilation.
6. Follow-up pass, after the main work:
   * the three impure-call rules of question 5, which let the stage 1
     sorries be removed and close the gap noted in section 7;
   * run-time checking of loop invariants (question 4);
   * when Core gains `requires` and `ensures`, run-time checking of
     those too.

If stage 1 goes badly, nothing has been lost and `GHOST_ARGS.md` can be
resumed from the parked branch.

## 11. References

1. J.-C. Filliâtre, L. Gondelman, A. Paskevich. "The Spirit of Ghost
   Code". CAV 2014. The same erasure theorem, with the same
   termination requirement. Ghost-ness is in the type system and
   erasure is a function.
2. S. Owens, M. Myreen, R. Kumar, Y. K. Tan. "Functional Big-Step
   Semantics". ESOP 2016. The case for clocked (fuel-based)
   interpreters over relational big-step.
