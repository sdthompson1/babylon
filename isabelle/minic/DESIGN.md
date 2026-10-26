# MiniC: design of the verified code generator (stages 3a and 3b)

This document is the design for the verified code generator that will
translate a linked, ghost-erased, match-compiled, normalized `CoreModule`
into "MiniC", a small fragment of C, and for the MiniC semantics, typing and
printer defined in this directory. Stage 3a produced the design and the
semantics; its decisions (the static size bound of section 3.2, the encoding
as a record in section 2.2, the global initialisation in section 3.7 and the
extern name map in section 3.9) were reviewed and accepted on 2026-10-23.
Stage 3b added the typing judgement (section 1.2), the printer and the
C-level validation of the example (section 11).

The theories in this directory:

| Theory | Contents |
| --- | --- |
| `MiniCSyntax.thy` | C types, expressions, statements, functions, programs; syntactic well-formedness |
| `MiniCMemory.thy` | bytes, block/offset pointers, the abstract integer encoding and its laws, the little-endian instance, load/store/copy/alloc/free |
| `MiniCSemantics.thy` | states, extern models, pure expression evaluation, the fuelled statement interpreter, `run_program` |
| `MiniCFuelMono.thy` | fuel monotonicity |
| `MiniCTyping.thy` | the typing judgement `program_well_typed`, and `expr_type_sound` |
| `MiniCPrint.thy` | the (unverified) printer to C, `print_program` |
| `MiniCExample.thy` | the hand-written example programs, their extern models, their evaluation and typing by `eval`, and the list `minic_examples` the driver exports |

They are part of the main `Babylon` session (`isabelle/ROOT`); the separate
`Babylon_MiniC` session of stage 3a is gone. To iterate on one theory
without rebuilding the session, use
`isabelle process -d . -l Babylon -T minic/<Theory>` from `isabelle/`.
`front_end/CodeExport.thy` exports `print_program` and `minic_examples` to
Haskell, and the driver `isabelle/Main.hs` prints an example to a `.c` file
(`Main --minic`, section 11).


## 1. The MiniC language

### 1.1 Overview

MiniC is the subset of C that the existing C code generator (`src/codegen.c`)
actually emits, cleaned up so that it has a simple semantics:

- Every variable is an object in byte-addressed memory. A *scalar* variable
  holds one C scalar: an exact-width integer (`int8_t` ... `uint64_t`) or a
  pointer (`char *` or `void *`). A *buffer* variable is a `char[n]` array
  whose size may be a run-time expression (a C99 VLA).
- Expressions are pure. They may read memory (`ME_Var` reads a scalar
  variable, `ME_Load` reads a scalar at an address) but cannot call, assign,
  store or allocate. Expression evaluation can still fail (undefined
  behaviour), for example a load from a dead block.
- Everything with an effect is a statement: declarations, assignment to a
  scalar variable, store through a pointer, `memmove`, `memset`, `if`,
  `while (1)`/`break`, blocks, calls (whose scalar result may be assigned to
  a scalar variable) and `return`. There is no `abort()`: MiniC has no
  defined abnormal termination, because the generated code never needs one
  (sections 3.2 and 3.3).
- Names are plain strings. The unverified printer (section 11) mangles them.
  An extern function carries its C name (`MF_Extern = Some cname`) and is
  printed under that name, unmangled.

The concrete grammar is in `MiniCSyntax.thy`. The following table says why
each construct is there (section 3 gives the lowering that uses it).

| Construct | Needed for |
| --- | --- |
| `CTy_Int s b` | all Babylon scalars; `bool` is `uint8_t` 0/1 |
| `CTy_CharPtr`, `CTy_VoidPtr` | addresses of aggregates / `ref` parameters; extern types. Semantically identical; the distinction is only for printing extern prototypes (`docs/c-interface.md`: extern types are `void *`) |
| `ME_Int s b i` | literals, tags, constant sizes and offsets |
| `ME_PtrSize` | `sizeof(void*)`, the size of an extern type and of the pointer in an array descriptor. A run-time value, because the pointer size is a parameter of the model |
| `ME_Var`, `ME_AddrOf` | reading a scalar variable; the address of any variable (`(char*)&x` for a scalar, `x` for a buffer) |
| `ME_Load ty p` | reading a scalar field/element out of a byte buffer (`memcpy(&tmp, p, sizeof tmp)`) |
| `ME_Unop`, `ME_Binop`, `ME_Cast` | Core's unary/binary operators and integer casts |
| `CB_Max` | variant sizes (`tag + max payload`) and `max(1, n)` for VLA sizes |
| `CB_Shl`, `CB_Shr` | Core's shifts, which C does not define in all cases (section 5.3) |
| `ME_PtrAdd` | field offsets, element addresses, the payload of a variant |
| `MS_DeclScalar`, `MS_DeclBuf` | locals and temporaries |
| `MS_Assign`, `MS_Store`, `MS_Copy`, `MS_Zero` | scalar assignment; writing a scalar into a buffer; aggregate copies (`memmove`); default values (`memset 0`) |
| `MS_If`, `MS_Loop`, `MS_Break` | Core `if`/`match`/`while` (`while` is `while (1) { if (!c) break; ... }` as in `codegen.c`) |
| `MS_Block` | Core blocks and match arms (fresh scope) |
| `MS_Call` | calls; the scalar result goes to a scalar variable, an aggregate result goes through a return-buffer pointer argument |
| `MS_Return` | return |

Deliberately omitted: `switch` (matches become `if` chains, which are easier
to print and to reason about), `for`/`while (c)` (one loop form), pointer
comparisons and pointer-integer conversions (never needed: executable Core
has no equality at extern types), `struct` types (aggregates are byte
buffers, exactly as `docs/c-interface.md` describes them), expression-level
side effects (calls, `++`, assignment), `goto`, floating point, bit-fields,
`static` locals, string literals (Core has none after elaboration: they are
array literals or hoisted constants).

### 1.2 Well-formedness and typing

`program_wf` (in `MiniCSyntax.thy`) is the small amount of static
well-formedness the interpreter relies on: distinct function and global
names, `main` exists as `int main(void)`, every call names a function of the
program with the right number of arguments, `break` only inside a loop,
integer literals in range.

`program_well_typed` (in `MiniCTyping.thy`) is the typing judgement, an
executable function. Its purpose is theorem 1 of section 8: a well-typed
program is one a C compiler accepts, so it checks what a C compiler checks
and the interpreter does not:

- every variable is declared before use; no name is declared twice in one
  scope (the parameters count as declared in the outermost scope of the
  body); no variable (global, parameter or local) has the name of a
  function, MiniC name or extern C name alike, since C has one namespace
  for both and the interpreter keeps them apart;
- `expr_type env e` gives the C type of an expression or `None`: the
  operands of a binop are integers of one type (except the count of a
  shift, which may have any integer type), comparisons and `!` yield
  `uint8_t`, loads and `ME_PtrAdd` need a pointer operand, casts are
  integer-to-integer or pointer-to-pointer, literals fit their type;
- assignments, stores, arguments, call results and returns are
  *compatible* with the declared type: identical, or both pointer types
  (`char *` and `void *` convert implicitly in C, and the semantics does not
  distinguish them: `val_has_ty (MV_Ptr p) ty = is_ptr_ty ty`);
- `return;` only in a void function, `return e;` only in a non-void one;
  the result of a call is assigned only if the function is non-void.

It does not check that a non-void body ends in a `return` (C does not
require it; falling off the end and using the result is UB in both), nor
`break` placement (`program_wf`). The lemma `expr_type_sound` shows that a
well-typed expression evaluates, when it evaluates, to a value of its type
(`val_has_ty`), given `valid_encoding` and an environment that describes the
state (`env_matches`). Statement-level soundness is not needed yet.

The printer uses `expr_type` too, to know the type of every arithmetic
result (section 11.2).


## 2. The memory model

### 2.1 Values, bytes, blocks

Memory (`MMem`) is a finite map from block numbers to byte lists, plus the
next block number. Blocks are never reused: a freed block disappears, so a
dangling pointer is detected forever. A pointer is `MP_Null` or
`MP_Addr block offset`, with `offset` a byte offset in `[0, size]` (one past
the end is allowed, as in C; dereferencing it is not).

A byte (`MByte`) is `MB_Undef` (never written), `MB_Byte n` (0..255), or
`MB_Frag block offset i`, fragment `i` of the stored pointer
`MP_Addr block offset`. Fragments are the CompCert device for storing a
pointer without an integer representation: a pointer reads back only from a
complete, in-order run of its fragments; any other byte pattern decodes as
undefined. The null pointer is stored as `ptr_size` zero bytes and all-zero
bytes read back as null (assumption A3 of section 5).

Expression values (`MVal`) are width-tagged integers `MV_Int s b i` (with
`i` in range) and pointers `MV_Ptr p`. Nothing else is ever stored or
computed: no Core values, no symbolic typed values.

A load of a scalar of type `ty` at `p` reads `ty_width ty` bytes and decodes
them; a store encodes and writes. `MS_Copy` (`memmove`) reads the source
bytes, undefined ones included, and writes them unchanged, so a copy of a
variant with uninitialised payload bytes is fine and the copy is just as
(un)defined as the original. Only decoding a scalar from a range containing
`MB_Undef` or a pointer fragment is undefined behaviour.

### 2.2 The integer encoding

The encoding is a record parameter `MEncoding` (pointer size, `encode`,
`decode`) with the validity predicate `valid_encoding`:

- the pointer size is positive and below `2^64` (added in stage 3b:
  `ME_PtrSize` evaluates to a `uint64_t` value unconditionally, so this is
  what makes that value well-formed; it is a consequence of A6, sizes fit
  `uint64_t`);
- an in-range integer of type `(s, b)` encodes to exactly `byte_width b`
  bytes, each < 256, and decodes back to itself (so encoding is injective,
  `valid_encoding_injective`);
- any `byte_width b` bytes decode to an in-range integer (no trap
  representations, C99 7.18.1.1);
- zero encodes as all-zero bytes (`calloc`/static zero-fill give Core
  default values; assumption A4).

Nothing fixes the byte order. `le_encoding` is the little-endian two's
complement instance, proved valid (`valid_le_encoding`), and is what makes
the interpreter runnable (`MiniCExample.thy`). The theorems of stages 4 to 6
will quantify over every valid encoding.

The encoding is a record with a validity predicate rather than a locale:
the semantics functions take `enc` as an explicit argument, so
`value`/`eval` work without locale interpretation and the code export in
stage 3b stays simple. The price is an explicit `valid_encoding enc`
hypothesis on every lemma that needs the laws.

### 2.3 How each Core type is laid out

Exactly as `docs/c-interface.md`:

| Core type | Bytes | Layout |
| --- | --- | --- |
| `bool` | 1 | `uint8_t`, 0 or 1 |
| `iN`/`uN` | N/8 | the encoding of the value at that type |
| extern type | `ptr_size` | a `void *`; the default value is null |
| record `{f1: T1, ..., fn: Tn}` | `Σ |Ti|` | fields in declaration order, packed, no padding |
| datatype with constructors `C0 .. Ck` | `tagsize + max_i |payload_i|` | tag (`uint8_t` if k+1 ≤ 256, `uint16_t` if ≤ 65536, else `uint32_t`) holding the constructor's index, then the payload; the bytes after the payload are unused and may be undefined |
| fixed array `T[n1, ..., nd]` | `|T| · Π ni` | elements contiguous in Fortran order (first index varies fastest): element `[i1, ..., id]` at `|T| · (i1 + n1·(i2 + n2·(...)))` |
| allocatable `T[*,...]` / incomplete `T[,...]` (d dims) | `ptr_size + 8d` | descriptor: a `char *` to the element data (laid out as a fixed array of the run-time sizes), then one `uint64_t` per dimension |
| type variable `T` | run-time | the size is a `uint64_t` parameter of the enclosing function |

Variant tags, descriptor sizes and the index arithmetic are all encoded
integers, so the generated code never observes byte order.

### 2.4 Stack, heap, globals

All three live in the one `MMem`:

- *Stack.* Every declaration (`MS_DeclScalar`, `MS_DeclBuf`) and every
  parameter binding allocates a fresh block of undefined bytes (a parameter
  block holds the argument value). The state records the blocks of the
  current scope (`MS_Stack`); leaving a scope (`exec_scope`, or returning
  from `call_fun`) frees them. Pointers into them are then dangling, as in C
  after the lifetime of an automatic object ends. Loop bodies, `if`
  branches and blocks are scopes; a loop body is a fresh scope per
  iteration.
- *Heap.* Only extern models allocate and free heap blocks (the generated
  code never calls `malloc`); the model gives them the whole memory.
- *Globals.* `run_program` allocates one block per global, zero-filled
  (static storage is zero-initialised in C), before calling `main`. Globals
  are never freed.

`mem_alloc` never fails: the model assumes the C implementation can provide
every automatic object the program declares (assumption A6). Heap exhaustion
is modelled by the extern (section 6).

### 2.5 Undefined behaviour

`eval_expr` returns `None`, and the statement interpreter `Inl MErr_UB`, for
anything a C compiler may miscompile and for anything implementation-defined
that section 5 does not assume: out-of-range arithmetic (every arithmetic
operator computes the mathematical result and requires it to fit the operand
type, which is stricter than C for unsigned types), division or modulo by
zero, shift counts outside `[0, width)`, out-of-range integer conversions
(to signed *and* unsigned types; C would wrap for unsigned, but the generated
code never relies on it), reads or writes outside a live block, null
dereference, pointer arithmetic leaving `[0, size]` of a live block,
decoding a scalar from undefined bytes or pointer fragments, a zero-sized
buffer declaration, reading a buffer variable as a scalar, calling a
function that does not exist, falling off the end of a non-void function,
`break` outside a loop, a mismatch between an argument and its parameter
type, and an extern model returning `None` (its precondition failed).

The model is deliberately *stricter* than C wherever that costs nothing:
everything MiniC defines, every conforming C implementation (under the
assumptions of section 5) defines in the same way, which is the direction
the unverified printer needs.

The one place where the model is *more permissive* than C is aliasing.
Memory is untyped bytes: a block has no declared type and no effective type
(C99 6.5p6), and `mem_load`/`mem_store` accept any scalar type at any
in-range offset of any live block. So MiniC defines, for example, storing an
`int32_t` into a `char[8]` buffer and loading it back, or storing an
`int32_t` into the first four bytes of a `uint64_t` scalar variable and then
reading the variable, both of which C99 6.5p7 (the "strict aliasing" rule)
forbids when done through a typed lvalue such as `*(int32_t *)p`. This is
sound only because of the printer obligation P1 of section 5.2: every access
through a pointer is printed as `memcpy`/`memmove`/`memset`, which are
character-type accesses and are permitted by 6.5p7 whatever the effective
type of the object; and the only typed accesses the printer emits are to
named scalar variables at their declared type (`ME_Var`, `MS_Assign`), which
the semantics also performs at the declared type (`MVar_Scalar ty`). The
generated code of section 3 never reads a location at a type other than the
one it was written at, but nothing in the semantics requires that, and the
justification is the printing convention, not the memory model.


## 3. The compilation scheme

### 3.1 Shape of the generator

One step, Core to MiniC, with no intermediate language. The generator is a
type-directed traversal in the style of `codegen.c`: lowering a Core term
produces a list of MiniC statements (declarations of temporaries and the
statements that fill them) and a *result expression*, which is the value for
a scalar-typed term and a `char *` pointer to the bytes for an
aggregate-typed term:

    lower_term :: CGEnv ⇒ CoreTerm ⇒ CGState ⇒ (MStmt list × MExpr × CGState)

`CGEnv` holds the datatype tables, the function signatures, the type
parameters in scope and the representation of each Core variable in scope
(section 3.5); `CGState` is a counter for fresh temporaries. Every lowered
term needs its Core type, which the generator recomputes with
`core_term_type` (the input is well-typed, so this always succeeds).

Why no intermediate language: the two things an IL would buy are (a)
separating "flatten terms into statements with temporaries" from "lay out
values as bytes", and (b) a smaller simulation proof per pass. For this
pipeline (a) is not a real separation, because the lowering of every term
form is determined by the layout (a record literal *is* a sequence of
byte copies at offsets), and an ANF-style Core IL would still need a
semantics and a typing theorem of its own, plus a pass proof. The stage 6
proof is organised by Core term form either way. The lemma shape for terms
is

    interp_term d fuel st tm = Inr v  ∧  state_rep R st mem ∧ tm lowers to (stmts, e)
      ⟹ ∃mem'. exec_stmts (stmts) from mem reaches mem' normally
             ∧ mem' extends mem (changes only fresh blocks)
             ∧ e evaluates in mem' to a value/pointer representing v

which is a one-level simulation with a frame condition, the same shape for
every form. The decision is reversible: if stage 6 finds the term cases too
large, the lowering of terms to statements can be split off later without
changing MiniC.

### 3.2 Sizes, offsets and the static size bound

The size of a (ground or generic) Core type is a `uint64_t` MiniC
expression built as in `get_size_of_type` of `codegen.c`:

    size(bool) = size(u8) = size(i8) = 1, ..., size(u64) = 8
    size(extern type) = ME_PtrSize
    size(T) = ME_Var "size$T"         (type parameter T of the enclosing function)
    size({f1: T1, ...}) = size(T1) + ...
    size(D<args>) = tagsize(D) + max_i size(payload_i[args/params])
    size(T[n1, ..., nd]) = size(T) * n1 * ... * nd
    size(T[*, ...]) = size(T[, ...]) = ME_PtrSize + 8d

and the offset of a field is the sum of the sizes of the fields before it.
Datatype acyclicity (a hypothesis of the theorems) makes `size` terminate.
When the type is ground the generator folds the expression to a literal,
except for `ME_PtrSize`, which stays symbolic (the printer prints
`sizeof(void*)`).

Sizes in a generic function are computed in `uint64_t` at run time from
the size parameters, and the generator emits the size expressions above
directly, with no run-time checks, exactly as `codegen.c` does. A Core run
does not care about sizes (a Core value has no size), so in principle a
Core program could instantiate a generic function at a type whose size
exceeds `2^64 - 1` bytes and run normally in Core while the `uint64_t`
arithmetic in C wraps. Such a program could not run on any real machine
(it would exhaust memory long before), so the theorems simply exclude it,
by a static hypothesis `core_module_sizeable` that an executable checker
establishes over the Core module:

1. **The call graph is acyclic.** Babylon has no recursion (the elaborator
   rejects self-recursive and mutually recursive declarations: `check_sccs`
   in `ElabModule.thy`), so every elaborated module satisfies this. The
   checker computes a topological order of the functions, callers before
   callees, and fails if there is none. No separate "no recursion"
   hypothesis is needed: it is part of this one.
2. **A bound per size parameter, computed top-down.** In that order, each
   function `f` gets an upper bound `B_f(T)` for every type parameter `T`:
   `main` has none; for every call site `f<ty1, ..., tym>` inside a function
   `g`, the bound `B_f(Ti)` is the maximum, over all call sites of `f` in
   the program, of `|tyi|` evaluated with `g`'s size parameters set to
   `g`'s bounds. Every size expression is built from sums, maxima and
   products by literal array dimensions of the size parameters, so it is
   monotone in them, and evaluating it at the bounds gives an upper bound
   on its value at every actual instantiation.
3. **Every size fits.** Every size and offset expression that the
   generator emits in the body of `f` (sections 3.3 to 3.6), evaluated at
   `B_f`, is below `2^64`; and every closed type of the program has a size
   below `2^64` (typedefs are expanded by the elaborator, so a tower of
   record typedefs is a closed type and is covered here).

This is an over-approximation (a function called as `f<big, small>` and
`f<small, big>` is bounded by `(big, big)` and could be rejected although
every actual instantiation fits), which only rejects contrived programs,
and it is linear in the size of the program; the exact alternative,
enumerating every instantiation reachable from `main`, can be exponential
in the call depth, like monomorphisation.

The soundness lemma, to be proved in stage 4 on the Core side: in every
state of a Core run from `main`, the current instantiation (`IS_TyArgs` in
`CoreInterp`) maps each type parameter of the current function `f` to a
closed type of size at most `B_f(T)`. It is an induction over the
interpreter whose only interesting case is the call: the callee's
instantiation is the call site's syntactic type arguments under the
caller's instantiation (`calleeTyArgs`), so monotonicity of `size` gives
the bound. Consequently every size expression the generated code evaluates
has a mathematical value below `2^64`, and since every intermediate value
of a monotone non-negative expression is at most its final value, the
`uint64_t` arithmetic computes it exactly. The theorem of section 8 thus
has a single conclusion, "corresponds", with no trap or abort anywhere.

*Rejected alternative:* run-time overflow guards on every size
computation, with `abort()` on overflow and a theorem concluding
"corresponds or aborts". They are local and cheap but add a statement form
and an error outcome to MiniC that nothing else needs, weaken the theorem,
and make the generated code differ from `codegen.c`. The only argument for
them was polymorphic recursion, which Babylon does not have.

### 3.3 Terms

Notation: `⟦tm⟧ = (S, e)` means `tm` lowers to statements `S` and result
`e`; `|ty|` is the size expression of section 3.2; `tmp` is a fresh name;
`e : ty` means the C scalar type of a Core scalar type. "Place" means the
address of the bytes of an aggregate. For a scalar-typed term the result is
its value; for an aggregate-typed term the result is a place.

| Core term | Lowering |
| --- | --- |
| `LitBool b` | `ME_Int Unsigned 8 (0/1)` |
| `LitInt i` | `ME_Int s b i` with `(s, b) = get_type_for_int i` (the type Core gives the literal) |
| `LitArray ty [t1..tn]` | `MS_DeclBuf tmp (max 1 (n·|ty|))`; for each `tk`: `⟦tk⟧`, then store (scalar) or `MS_Copy` (aggregate) into `tmp + k·|ty|`; result `ME_AddrOf tmp` |
| `Var x` | by the representation of `x` (section 3.5): the value of a scalar variable, a load through a pointer, or a place |
| `Cast (iN/uN) t` | `ME_Cast (CTy_Int s b) ⟦t⟧` |
| `Cast (T[, ...]) t`, `t : T[n1, ..]` (fixed to descriptor) | declare a descriptor buffer `tmp` of size `ME_PtrSize + 8d`; `MS_Store CharPtr tmp ⟦t⟧`; store each `nk` as a `uint64_t` at `tmp + ptrsize + 8k`; result `ME_AddrOf tmp` |
| `Cast (T[n1, ..]) t`, `t : T[, ..]` (descriptor to fixed) | result `ME_Load CharPtr ⟦t⟧` (the data pointer). Core raises `RuntimeError` if the run-time sizes differ from the cast's, so no check is generated |
| `Cast` between dims of the same category | `⟦t⟧` |
| `Unop Negate/Complement/Not t` | `ME_Unop CU_Neg/CU_Compl/CU_Not ⟦t⟧` |
| `Binop op t1 t2`, arithmetic, bitwise, comparison | `ME_Binop ⟦t1⟧ ⟦t2⟧` (Core requires identical operand types; comparisons yield `uint8_t`) |
| `Binop ShiftLeft/ShiftRight` | `ME_Binop CB_Shl/CB_Shr`, Core semantics, printed as the idiom of section 5.3 |
| `Binop And/Or/Implies t1 t2` | `MS_DeclScalar tmp u8; tmp = ⟦t1⟧` (for `Implies`: `!⟦t1⟧`); `MS_If tmp [⟦t2⟧; tmp = e2] []` for `And`, `MS_If tmp [] [⟦t2⟧; tmp = e2]` for `Or`/`Implies`; result `ME_Var tmp`. The right operand's statements run only when needed, which is Core's short-circuit semantics |
| `Let x t1 t2` | `⟦t1⟧`; bind `x`: scalar: `MS_DeclScalar x ty; x = e1`; aggregate: `MS_DeclScalar x CharPtr; x = e1` (an alias of the place, no copy; see section 3.5); then `⟦t2⟧` |
| `FunctionCall f tys args` (pure) | section 3.4 |
| `VariantCtor C tys t` (type `D<..>`) | `MS_DeclBuf tmp |D<..>|`; `MS_Zero tmp |D<..>|`; `MS_Store tagty tmp (index of C)`; `⟦t⟧` copied/stored at `tmp + tagsize`; result `ME_AddrOf tmp`. `codegen_variant` leaves the bytes after the payload undefined; the `MS_Zero` is a stage 3b change (section 11.4): gcc's `-Wuninitialized` reports the later `memmove` of such a buffer under `-O2` with glibc's fortified `memmove`, so every variant value is fully defined instead, at the cost of one `memset` per construction |
| `Record [(f1, t1) ..]` | `MS_DeclBuf tmp |rec|`; each field copied/stored at its offset |
| `RecordProj t f` | place `⟦t⟧ + offset(f)`; if the field is scalar, `ME_Load ty` of it |
| `VariantProj t C` | place `⟦t⟧ + tagsize`; load if scalar. Core raises `RuntimeError` if the constructor differs, so no check |
| `ArrayProj t [i1 .. id]`, fixed dims | place `⟦t⟧ + |T| · (i1 + n1·(i2 + ...))` in `uint64_t`; load if scalar. Core raises `RuntimeError` for an out-of-bounds index, so no bounds check; and in-bounds index arithmetic cannot overflow when the array fits in memory (section 4) |
| `ArrayProj t [..]`, descriptor | `data = ME_Load CharPtr ⟦t⟧`, dims `nk = ME_Load u64 (⟦t⟧ + ptrsize + 8k)`, then as above |
| `Match s arms` (flat patterns) | `⟦s⟧`; for a variant scrutinee `tag = ME_Load tagty ⟦s⟧`, for a bool/int scrutinee `tag = ⟦s⟧`; declare the result `tmp` (scalar or buffer of the arm type); an `MS_If` chain comparing `tag` with each arm's literal (constructor index, `0/1`, or integer), each arm `⟦body⟧` copied/stored into `tmp`; the *last* arm is the final `else`, unconditionally, whether it is a wildcard or not. Core picks the first arm whose literal matches and raises `RuntimeError` when none does, so when the last arm is reached in a normal Core run its literal is the one that matches, and the no-match case needs no code at all (`codegen.c`'s `switch` without `default` falls through in the same way). A match with no arms always raises in Core; it lowers to the declaration of `tmp` alone. Result `tmp` |
| `Sizeof t`, descriptor | 1-d: `ME_Load u64 (⟦t⟧ + ptrsize)`; d-d: a record temp filled with the d loads |
| `Sizeof t`, fixed | literals (a `uint64_t` literal, or a record temp of them) |
| `Default ty` | scalar: `ME_Int s b 0` or null; aggregate: `MS_DeclBuf tmp (max 1 |ty|); MS_Zero tmp |ty|`. Correct because the default value of every type is all-zero bytes: false, 0, null, records of defaults, the first constructor (tag 0) with the default payload, fixed arrays of defaults, empty allocatable arrays (null pointer, zero sizes). Stage 4 proves this (`default_value_rep_zero`) |

The match-compiler's output (stage 1) is handled by the `Match` row: it
emits `CoreTm_Match`/`CoreStmt_Match` whose scrutinees are
`CoreTm_Var`, `CoreTm_VariantProj` and `CoreTm_RecordProj` chains over the
variable `match@@n` that the elaborator bound in a `Let` (terms) or
`VarDecl` (statements), and whose patterns are flat. Projection chains
lower to pointer arithmetic with no copies, so re-evaluating the scrutinee
at each level of the tree is free. Pattern variables do not exist in Core:
the elaborator binds them with `Let`s (terms) or `VarDecl`s (statements) of
projections of `match@@n` inside the arm body, which are ordinary terms and
statements here.

Ghost constructs (`Quantifier`, `Allocated`, math types) cannot occur in a
ghost-free module and are not handled.

### 3.4 Calls, size passing, `ref` arguments

A Core function `f<T1..Tm>(a1: ty1 [ref], ..., an: tyn [ref]): rty` becomes
the MiniC function

    [ret$ : char*]           if rty is an aggregate other than the unit type {}
    size$T1 .. size$Tm : u64
    a1 .. an : CTy            scalar by-value parameter: its C scalar type;
                              aggregate by-value parameter, or ref: char*
    returning: rty's scalar type; void for aggregates and for the unit type

which matches "Calling C Functions from Babylon" in `docs/c-interface.md`
(ghost arguments no longer exist). The unit type `{}` (the return type the
elaborator gives a procedure, with an implicit `return {}` at the end of the
body) is treated as `void`: no return buffer and `return;`. Core cannot
distinguish a procedure from a function declared `: {}`, so both must get
the same prototype; `codegen.c` was changed (October 2026) to agree, as
before then it gave an explicitly `{}`-returning function a `ret`
parameter like any other aggregate. (`test/cases/codegen/UnitReturn.b`
exercises this, including an extern.)

A call `f<ty1..tym>(e1..en)` lowers to:

1. if `rty` is a non-unit aggregate, `MS_DeclBuf ret (max 1 |rty|)`;
2. for each argument: a scalar by-value argument is `⟦ei⟧`; an aggregate
   by-value argument is the place `⟦ei⟧` (no copy, as in `codegen.c`); a
   `ref` argument is the address of the lvalue `ei` (section 3.5);
3. `MS_Call x f (ret?, |ty1|, ..., |tym|, args)` where `x` is a fresh
   scalar for a scalar result, none otherwise;
4. result: `ME_Var x`, or `ME_AddrOf ret`, or nothing for unit.

Core evaluates all arguments (as lvalues and rvalues) before the call and
the generated code does the same; argument expressions are pure, so the
order does not matter. Generic functions receive one `uint64_t` size per
type parameter and compute every size and offset from them (section 3.2);
there is no monomorphisation.

**Aliasing hypothesis.** Core binds a `ref` parameter to an address and a
*path* (`IS_Refs`) that is re-resolved on every access, and a by-value
parameter to a *copy* of the argument. MiniC passes pointers in both cases.
The two agree only if no `ref` argument overlaps another argument of the
same call: if `f(ref a[0], ref a)` reallocated `a` through its second
parameter and then wrote through its first, Core would write into the new
array while C writes into freed memory; if `f(x, ref x)` wrote through its
second parameter and then read its first, Core would see the old copy and
C the new value. Babylon's verifier rejects such calls
(`verify_aliasing` in `src/verifier_terms.c`: for every pair of arguments
of which at least one is `ref`, the two lvalue chains must not overlap,
with array indices compared by the SMT solver), but neither the Core
typechecker nor `CoreInterp` checks it. The simulation theorem therefore
needs the hypothesis that the Core run never performs such a call. Since
the hypothesis is about the run, not the program, the proposal for stage 4
is:

> **Proposal (Core change, stage 4):** in `interp_function_call`, after
> resolving the arguments, raise `RuntimeError` if two arguments, at least
> one of which is bound `Ref`, resolve to lvalues `(addr, path)` with the
> same address and with one path a prefix of the other (ignoring
> `LVPath_ArrayCast` steps). For this, by-value arguments that are lvalues
> need to be resolved too, including those with a read-only base (a
> "readable lvalue" variant of `interp_writable_lvalue`). Non-lvalue
> arguments cannot alias anything. This mirrors the verifier exactly (the
> verifier's SMT index comparison becomes an actual comparison of the
> index values) and makes the condition part of "the Core run reaches a
> normal result", exactly as stage 2 did for copies of allocated values.

The alternative, a hypothesis stated over an instrumented or trace-producing
Core interpreter, is heavier and is not recommended.

### 3.5 Variables, `ref` locals, lazy references

The generator's environment records, for each Core variable in scope, how
it is represented:

| Core binding | MiniC representation | Reading `x` | Address of `x` |
| --- | --- | --- | --- |
| mutable local (`VarDecl Var`, `VarDeclCall`) of scalar type | `MS_DeclScalar x ty` | `ME_Var x` | `ME_AddrOf x` |
| mutable local of aggregate type | `MS_DeclBuf x (max 1 |ty|)` | place `ME_AddrOf x` | `ME_AddrOf x` |
| by-value parameter of scalar type | scalar parameter | `ME_Var x` | `ME_AddrOf x` |
| by-value parameter of aggregate type | `char *` parameter | place `ME_Var x` | `ME_Var x` |
| `Let`-bound of scalar type | `MS_DeclScalar x ty` | `ME_Var x` | `ME_AddrOf x` |
| `Let`-bound of aggregate type | `MS_DeclScalar x CharPtr` holding the place of the rhs | place `ME_Var x` | `ME_Var x` |
| `ref` parameter (any type) | `char *` parameter | `ME_Load ty (ME_Var x)` if scalar, else place `ME_Var x` | `ME_Var x` |
| `ref` local, not lazy | `MS_DeclScalar x CharPtr` = address of the lvalue at declaration | as a `ref` parameter | `ME_Var x` |
| `ref` local, lazy | no MiniC variable; the generator remembers the lvalue term with its array indices frozen into fresh `uint64_t` locals | the address is recomputed from the base variable and the frozen indices at every use | ditto |
| global constant | global variable (section 3.7) | `ME_Var g` / place `ME_AddrOf g` | `ME_AddrOf g` |
| type parameter `T` | `uint64_t` parameter `size$T` | | |

*Lazy references* (`needs_lazy_ref` in `codegen.c`): the address of an
element of an allocatable array is only valid until the array is
reallocated (freed and allocated again through a `ref` to the array). Core
re-resolves the path at every access, so a Core `ref r = a[i]` followed by
a reallocation of `a` and a use of `r` accesses element `i` of the *new*
array (or raises `RuntimeError` if `i` is now out of range). To match, a
`ref` local whose lvalue passes through an allocatable-array projection
(`a[i]`, `a[i].f`, `r[i]` for a `ref` parameter `r` of allocatable type,
...) is not represented by a pointer but by the lvalue term itself, with
each index expression evaluated once, at the declaration, into a fresh
`uint64_t` local (Core evaluates the indices once too: `interp_writable_lvalue`
stores the index *values* in the path). Every use re-emits the address
computation. A `ref` parameter is never lazy: the callee cannot reach the
array the pointer points into except through its own `ref` parameters,
which the aliasing hypothesis makes disjoint, so the pointer stays valid
for the whole call.

Refs through a variant payload (`ref r = v.C`) or through an array cast
are stable pointers: the bytes do not move. If the variant is re-tagged
during `r`'s lifetime, Core raises `RuntimeError` on the next use, so no
correspondence is required; if it is overwritten with the same constructor,
both sides read the new payload.

*A `ref` to a read-only base* (a const local or a global): Core copies the
value (`bind_const_local`) instead of aliasing. The generated code aliases
(a pointer into the base). The two agree because neither the base nor the
new variable can be written while the latter is live. The same holds for a
`Let`-bound aggregate (the `Let` body is a pure term) and for a by-value
aggregate parameter (the caller is suspended; by the aliasing hypothesis the
callee's `ref` parameters do not overlap it). Section 4 says how the
representation relation accommodates this sharing.

### 3.6 Statements

| Core statement | Lowering |
| --- | --- |
| `VarDecl NotGhost x Var ty t` | declare `x` as in section 3.5; `⟦t⟧`; `MS_Assign x e` (scalar) or `MS_Copy (ME_AddrOf x) e |ty|` (aggregate) |
| `VarDeclCall x ty cast f tys args` | declare `x`; the call of section 3.4; apply the cast (an integer cast of the scalar result, or an array cast of the result place as in section 3.3); copy/assign into `x` |
| `VarDecl NotGhost r Ref ty lv` | section 3.5: either `MS_DeclScalar r CharPtr; r = address(lv)`, or (lazy) freeze the indices of `lv` into fresh locals and record the term |
| `Assign NotGhost ty lv t` | `⟦t⟧`; `a = address(lv)`; `MS_Store ty a e` (scalar) or `MS_Copy a e |ty|` (aggregate; `memmove`, since `lv` and `t` may overlap, e.g. `x := x`). Core's copy check (stage 2) makes copying an allocated value a `RuntimeError`, so the byte copy never duplicates ownership of a heap block |
| `AssignCall lv cast f tys args` | freeze the index expressions of `lv` (Core resolves the lhs before the call); the call; the cast; then compute the address of `lv` from the frozen indices (after the call, because the call may have reallocated an array the lvalue goes through) and copy/store |
| `Swap NotGhost lv1 lv2` | `MS_DeclBuf/DeclScalar tmp`; `tmp := lv1; lv1 := lv2; lv2 := tmp` as three copies/stores (addresses computed once; the lvalues are of the same type and either identical or disjoint). Ownership of allocated values moves with the bytes |
| `Return t` | scalar: `⟦t⟧; MS_Return (Some e)`; unit: `MS_Return None`; aggregate: `⟦t⟧; MS_Copy (ME_Var ret$) e |rty|; MS_Return None`. (The copy check in `call_body` makes returning an allocated value a `RuntimeError`) |
| `While NotGhost c [] None body` | `MS_Loop (⟦c⟧ @ [MS_If (ME_Unop CU_Not e) [MS_Break] []] @ ⟦body⟧)` |
| `Match NotGhost s arms` | as the term form, with each arm's statements in an `MS_Block` (a fresh scope, as `interp_statement` runs it) and no result temporary |
| `Block body` | `MS_Block ⟦body⟧` |

Statements that a ghost-free module cannot contain (`Fix`, `Obtain`, `Use`,
`Assert`, `Assume`, `ShowHide`, ghost-flagged statements, invariants,
decreases terms) are not handled.

Function bodies: the statements of the body, with sizes and offsets as
inline expressions over the size parameters (section 3.2). Core's
`call_body` raises `RuntimeError` if the body falls off the end without
`return`, so the generated body need not end with one.

### 3.7 Global constants

`CM_GlobalVars` maps each global to a `CoreValue`; its type is in
`TE_GlobalVars` of the type environment. Each global `g` becomes a MiniC
global (`MG_Scalar ty` or `MG_Buf |ty|`), which C zero-initialises, and the
generated `main` begins with statements that store its value:

- scalars: `MS_Assign g lit`;
- records, variants, fixed arrays: stores of the scalar leaves at their
  offsets (variant tag included; unused payload bytes stay zero);
- a `CV_Array` at an allocatable or incomplete array type (a hoisted string
  literal `Mod.str@@n` has the fixed type `u8[N]`, but a constant declared
  at type `u8[]` has an incomplete type and the same kind of value): the
  element data goes into a separate global buffer `g$data$k` (one per
  occurrence, initialised like a fixed array), and the descriptor part of
  `g` is filled with `MS_Store CharPtr (ME_AddrOf g$data$k)` and the sizes.
  The pointer is an address of a global, which is why these constants
  cannot be byte literals; if all sizes are zero no data buffer is made and
  the pointer stays null;
- `CV_Extern _ _ 0` is null; a non-zero handle cannot occur in a
  compile-time value (the generator rejects it);
- `CV_Int`/`CV_Real` cannot occur (ghost-free).

Storing a literal is not a copy of an allocated value, so no ownership
question arises; the data buffers are static and never freed (a constant of
allocatable type with a non-empty value would be an "allocated" constant,
which Babylon's verifier rejects; the design handles it anyway).

Constants are initialised at program start rather than by the lazily
initialised accessor functions of `docs/c-interface.md` ("Accessing Babylon
Constants from C"). Reasons: the output is one `.c` file and no external C
code reads Babylon constants, so the accessor convention buys nothing; a
plain global with static initialisation in `main` is one statement form
(`MS_Store`) the generator already has, needs no `static` locals or
function-level laziness in MiniC, and its correctness is the ordinary
"stores establish the representation" lemma. Static initialiser lists
(`= {10, 0, 0, 0}`) are out, since they would fix the byte order. The cost
is that a C program that calls into the generated code without going
through its `main` sees zeroed constants; such programs are not supported.

### 3.8 The generated `main`

    int main(void) { <global initialisation>; <Core main>(); return 0; }

that is, an `MFun` named `main` with `MF_Ret = Some CTy_I32` whose body is
the stores of section 3.7, then `MS_Call None "<Mod>.main" []`, then
`MS_Return (Some 0)`. The name of the Core main function is a parameter of
the generator (the driver knows the root module). The Core main is a
procedure (`{}` return, no parameters, no type parameters); the generator
checks this. `run_program` in the semantics mirrors the C start-up: allocate
the globals zero-filled, call `main`, return its `int`.

### 3.9 Extern functions and their C names

An extern Core function (`CF_Body = None`) becomes an `MFun` with
`MF_Extern = Some cname` and no body; its parameter list is computed as in
section 3.4, so its prototype (section 11.2) is the one
`docs/c-interface.md` prescribes, and the existing implementations
(`packages/coretypes/src/Array.c`, `Test.c`) work unchanged. Calls to it
are ordinary `MS_Call`s; the interpreter dispatches on `MF_Extern` to the
model (section 6).

How `cname` reaches the generator: the elaborator sees `DF_ExternName` but
drops it, and nothing in Core records it. The chosen route is a *side
map*, not a Core change: `elab_program` additionally returns a map
from the qualified Core name of each extern function to its C name
(`DF_ExternName` if given, otherwise the unqualified Babylon name, as
`get_extern_name` in `codegen.c`); `whole_program_link` is not involved
(names are qualified, so the maps of the modules are simply united); the
driver passes the map to the generator, which uses the entry for each
`CF_Body = None` function (and falls back to the unqualified name if there is
none). This keeps `CoreModule`, `InterpFun`, the linker and all their proofs
untouched, which is right because the C name is irrelevant to every theorem
(only the unverified printer consumes it). The rejected alternative, a
field `CF_ExternName :: string option` on `CoreFunction`, is more robust
against the map and the module going out of sync but touches every
construction site of `CoreFunction` in the elaborator and linker.
Implementation is stage 5 work.


## 4. The representation relation (stage 4 preview)

This stage only fixes the shape; stage 4 defines and proves it. The relation
is parametrised by the type environment (datatype tables), a valid encoding,
and a *handle map* `hmap :: nat ⇒ MPtr` with `hmap 0 = MP_Null`, injective,
giving the MiniC pointer value of each Core extern handle (section 6).

`rep_val env enc hmap mem ty v bs` ("`bs` are the `|ty|` bytes of `v` at type
`ty`, with heap blocks in `mem`"):

- `CV_Bool b`: `bs = encode u8 (if b then 1 else 0)`;
- `CV_FiniteInt s b i`: `bs = encode s b i`;
- `CV_Record fs` at a record type: the concatenation of the fields' byte
  lists;
- `CV_Variant C p` at `D<args>`: `encode tagty (index of C) @ payload bytes @
  junk`, where `junk` is any bytes (undefined included) padding to `|D<args>|`;
- `CV_Array sizes elems` at fixed dims: the elements' byte lists in Fortran
  order;
- `CV_Array sizes elems` at allocatable/incomplete dims: `encode_ptr p @
  encode u64 sizes`; if the element count is zero `p` is null or the start
  of a live heap block; otherwise `p = MP_Addr blk 0` with `blk` a live block
  of exactly `count · |elem|` bytes whose contents represent the elements;
- `CV_Extern n l h` at `CoreTy_Extern n l`: `bs = encode_ptr (hmap h)`;
- in all cases `|ty| < 2^64` (so that every size, offset and index
  computation of section 3 fits `uint64_t`; `core_module_sizeable` of
  section 3.2 guarantees this for every type a Core run instantiates, and
  the extern hypothesis delivers it for arrays an extern allocates).

`state_rep` relates a Core `InterpState` to a MiniC state (memory, globals,
locals, world): the worlds are equal; every global is represented in its
block; every cell of `IS_Store` has a *region* (block, offset) whose bytes
represent its value; `IS_Locals`/`IS_Refs`/`IS_TyArgs` of the current frame
map to MiniC variables as in section 3.5 (a `ref` to a pointer variable
whose value is the region of the cell at the path, or to a lazy term; a type
parameter to a size variable holding `|T|`); MiniC may have any number of
extra blocks (temporaries, dead frames' leftovers do not exist, since scopes
free them).

*Ownership.* Because stage 2 makes copying an allocated value a
`RuntimeError`, a normal Core run never has two *mutable* cells holding the
same allocated array; dropping one (leaving a scope) is a leak in C and
harmless to the theorem (the block simply stays live and unreferenced).
The relation states ownership as: regions of distinct cells are disjoint and
heap blocks reachable from distinct cells are distinct, *except* that a
cell created by `bind_const_local` (a by-value parameter, a `Let` variable,
a `ref` to a read-only base) may share its region and heap blocks with the
cell it was copied from. Sharing is sound because such a const cell and its
origin are never written while both are live: a `Let` body is pure; a
by-value parameter's origin belongs to a suspended caller and (aliasing
hypothesis) is not reachable through the callee's `ref` parameters; a
read-only base is never written. The invariant that the simulation
maintains is therefore "every location writable from the current frame
(its mutable cells, its `ref` targets, and the heap blocks reachable from
them) is referenced by no other live cell", which every statement form
preserves and every call establishes for the callee.

A by-value *scalar* parameter is a genuine copy (C passes it by value) and
needs no exception.


## 5. The C dialect

### 5.1 Standard version

**Target: C99** (ISO/IEC 9899:1999), with the explicit assumptions A1 to A8
below. Reasons:

- `docs/c-interface.md`, `Array.c` and `Test.c` already assume C99
  (`<stdint.h>`, `<stdbool.h>`, `SIZE_MAX`), and the existing compiler
  (`src/codegen.c`) targets "C99 or later" with the same assumption list,
  so this is the established baseline of the project.
- The generated code needs variable-length arrays for temporaries and
  locals of generic type. VLAs are mandatory in C99; C11 and C17 make them
  optional (`__STDC_NO_VLA__`), and C23 makes variably-modified *types*
  mandatory but automatic VLA *objects* still optional. So a later standard
  would not reduce the assumption list here; it would add one.
- C23 would make two's complement a theorem of the standard and remove A2,
  but C23 toolchains are not yet universal (the sandbox's gcc 13 has only
  partial `-std=c2x` support) and every target the project cares about
  satisfies A2 anyway. If C23 is adopted later, nothing in MiniC changes;
  only A2 is deleted from this list.

`check_example.sh` (section 11) compiles the examples with
`gcc -std=c99 -Wall -Wextra -pedantic -Werror`, and with `-std=c11` and
`-std=c17`, which accept the same code when VLAs are supported.

### 5.2 Assumptions about the C implementation

All of them are checkable at compile time or are properties of every
mainstream target; the printer emits `#if`/`#error` guards for A1, A2 and
A5 at the top of the generated file (section 11.2).

- **A1. `CHAR_BIT` is 8**, so `sizeof(intN_t) = N/8` and the byte counts of
  section 2.3 are exact. (Follows from the existence of `uint8_t`, which
  must have exactly 8 bits with no padding; stated anyway.)
- **A2. Two's complement, no padding, no traps** for every signed integer
  type the generated code can be promoted to (`int`, `long`, ...), not only
  the exact-width types (which C99 7.18.1.1 already guarantees). Observable
  only in `~`, `&`, `|`, `^` on negative values of narrow signed types
  (promoted to `int`) and in the shift idiom of section 5.3; Core's
  semantics for these are two's complement (`and`/`or`/`xor` on `int`,
  complement `-i - 1`).
- **A3. A null pointer is all-zero bytes, and all-zero bytes read back as a
  null pointer.** `docs/c-interface.md` assumes it for the default value of
  extern types, `free_array` writes `NULL` into descriptors, `calloc` and
  static storage produce zero bytes that are read as null descriptors.
  Built into `encode_ptr`/`decode_ptr`.
- **A4. Zero is all-zero bytes at every integer width.** A theorem under A2,
  but the encoding is abstract, so it is a law of `valid_encoding`.
- **A5. Right shift of a negative signed value is an arithmetic shift**
  (implementation-defined in every C version). `CB_Shr` has Core's
  `drop_bit` semantics, which on negative values is the arithmetic shift.
- **A6. Memory for automatic objects is available.** `mem_alloc` never
  fails, so the model has no stack overflow and no VLA failure; the C
  implementation is assumed to provide every automatic object the program
  declares, and every object size fits `size_t` (sizes are computed in
  `uint64_t` and passed to `memmove`/`memset`/VLA declarations; a size that
  does not fit `size_t` could not be allocated on that target anyway).
- **A7. The exact-width types `int8_t` ... `uint64_t` exist** (C99 makes
  them optional; `docs/c-interface.md` requires them).
- **A8. `memmove`, `memset` and the pointer arithmetic the printer emits
  behave as the standard says** (no assumption beyond C99, listed so that
  the list is complete: the generated code uses no other library
  functions, and all pointer arithmetic stays inside one object).

Not assumed: anything about `sizeof(int)`, `sizeof(void*)` (a parameter),
endianness (abstract encoding), alignment (every multi-byte access to a
buffer goes through `memmove`/`memcpy`), anything about strict aliasing or
effective types (C99 6.5p6-7: every access through a pointer is a
character-type access, which is always permitted, and the only typed
accesses are to scalar variables at their declared type; see P1 below and
section 2.5), the result of out-of-range conversion to a signed type (UB in
MiniC; never performed by a Core run that reaches a normal result), unsigned
wrap-around (UB in MiniC; never relied on), the value of an uninitialised
object (UB to decode).

**Obligation on the printer.** The assumptions above are about
the C implementation; the following is a constraint on how MiniC is printed,
without which the untyped memory model of section 2 would not be sound
against C.

- **P1. No typed access through a pointer.** `ME_Load ty p` is printed as a
  `memcpy` of `sizeof(T)` bytes from `p` into a temporary of type `T`, and
  `MS_Store ty p e` as a `memcpy` from a temporary into `p` (or as helper
  functions that do exactly that); `MS_Copy` and `MS_Zero` are `memmove` and
  `memset`. The printer never emits `*(T *)p` for any `T` other than `char`,
  and never folds `ME_Load ty (ME_AddrOf x)` or `MS_Store ty (ME_AddrOf x) e`
  into a direct read or write of `x`, since that is only correct when `ty` is
  the declared type of `x`, which the printer cannot see. The only accesses
  printed through a typed lvalue are `ME_Var x` and `MS_Assign x e`, which
  are reads and writes of the scalar variable `x` at its own declared type,
  and `ME_AddrOf x` is `(char *)&x` for a scalar and `x` for a buffer.
  `codegen.c` already follows this convention everywhere (`memmove` for
  reads through `ref` parameters and lazy references, `memcpy` for field
  and element reads, the shift helpers of section 5.3), and so does
  `Array.c` for descriptors.

### 5.3 Shifts

Core's `ShiftLeft`/`ShiftRight` require `0 ≤ count < width` and a result
that fits the operand type; otherwise `RuntimeError`. MiniC's `CB_Shl` and
`CB_Shr` have exactly that semantics (the count may be an integer of any
width; the result has the left operand's type). The printer lowers them to
the idiom of `shift_binop` in `codegen.c`, as helper functions emitted once
per type at the top of the file (`print_helpers_for` in `MiniCPrint.thy`):

    static inline int32_t bab_shl_i32(int32_t x, uint64_t n) {
        uint32_t u = (((uint32_t) x) + 0u) << n;        /* unsigned, so defined; +0u defeats promotion to int */
        int32_t r; memcpy(&r, &u, sizeof r); return r;  /* bytes back, no signed conversion */
    }
    static inline uint16_t bab_shl_u16(uint16_t x, uint64_t n) { return (uint16_t) ((x + 0u) << n); }
    static inline int64_t  bab_shr_i64(int64_t x, uint64_t n) { return (int64_t) (x >> n); }   /* A5 */

Why this is right under the MiniC precondition: for a signed left shift
whose mathematical result `r = x · 2^n` fits the type, the unsigned
computation gives `(x mod 2^W) · 2^n mod 2^W = r mod 2^W`, and copying
those bytes back yields `r` by A2. Unsigned shifts are defined by the
standard once promotion to a signed type is defeated by `+ 0u` (if `int`
is wider than the operand, `x + 0u` has type `unsigned int` or wider; if
`int` is narrower than or equal to the operand, no promotion happens). The
count is converted to the helper's parameter type exactly, since it is
below the width.


## 6. Extern functions on the MiniC side

### 6.1 The model

An extern function is modelled by a value of type

    'w MExtern = 'w ⇒ MMem ⇒ MVal list ⇒ ('w × MMem × MVal option) option

keyed by the Core function name in the interpreter's context
(`MC_Externs`). It receives the world, the whole memory and the argument
values exactly as C would (return-buffer pointer first, then one `uint64_t`
per type parameter, then the arguments: scalars by value, aggregates and
`ref`s as pointers), and returns the new world, the new memory and the
scalar result (`None` for void). `None` overall means the call was outside
the model's precondition (for example a dangling pointer argument) and is
undefined behaviour. The model may read and write memory through the
pointers it was given and may allocate and free heap blocks; this is what
`alloc_array` and `free_array` do. `MiniCExample.thy` contains models of
`alloc_array`, `free_array` and the `print_*` functions of `Test.c` written
in this style (a `print_*` model appends to a world that is a list of
printed values); supplying a model is a few lines per function.

### 6.2 The hypothesis of the final theorem (sketch)

Stage 4 will state, for an extern `f` with Core implementation
`E :: 'w ExternFunc` and MiniC model `M :: 'w MExtern`, a relation
`extern_rep env enc hmap finfo E M` of roughly this form:

> For every world `w`, type instantiation `tys` of `f`'s type parameters,
> Core argument values `vs` with the instantiated parameter types, memory
> `mem` and MiniC argument values `as` such that `as` represent `vs`
> (scalars by value; aggregates and `ref`s as pointers to regions of `mem`
> whose bytes represent the values by `rep_val`; the size arguments equal
> `|tys|`; the return-buffer pointer, if any, points to a writable region of
> `|rty|` bytes), with all these regions pairwise disjoint:
> if `E w vs = (w', refUpdates, ret)` then `M w mem as = Some (w', mem', r)`
> where
>   - `mem'` agrees with `mem` on every byte outside the `ref` regions, the
>     return region and the heap blocks owned by the descriptors among the
>     arguments (frame condition), and does not free any other block;
>   - the `ref` regions in `mem'` represent `refUpdates` and the return
>     region (or `r`) represents `ret`, using `hmap` for extern handles (so
>     `hmap` is a fixed injection, shared by all externs: a handle Core
>     creates corresponds to one MiniC pointer, and only handle 0 is null);
>   - every heap block referenced by a represented array in `mem'` is live,
>     of the right size, and owned by exactly one descriptor among the
>     results.

Because the Core `ExternFunc` is total and deterministic in `(w, vs)`,
whether an allocation succeeds is decided by `w`: `E` returns `false` (and
unchanged refs) in exactly the worlds where the allocation "fails", and the
hypothesis forces `M` to return the representation of that same result, so
the MiniC extern fails exactly when the Core one does and never with `None`
on well-represented arguments. For `Test.c`'s `alloc_array`, which `abort`s
on exhaustion, the Core and MiniC models both always succeed, and the
correspondence with the real C program holds under A6 extended to the heap.

Externs are called in Core with the caller's `ref` lvalues resolved and
their updates written back by `apply_ref_updates`; on the MiniC side the
extern writes through the pointers directly. The regions are disjoint by
the aliasing hypothesis, so the two agree.


## 7. The example (`MiniCExample.thy`)

The hand-written program `example_prog` exercises every feature the
deliverable lists, written exactly as the generator of section 3 would
write it (names unmangled, sizes as expressions):

- a record `{x: i32, y: i32}` (8 bytes) built field by field;
- a variant `Shape = Circle(i32) | Rect({x: i32, y: i32})` (1 + 8 bytes),
  constructed with `Rect`, matched with an `if` chain on the tag;
- a fixed array `i32[3]` built with stores and summed by a loop;
- an allocatable array `i32[*]` (descriptor of `ptrsize + 8` bytes),
  allocated by the extern `alloc_array`, filled, summed with a generic
  function, and freed by `free_array`;
- a generic function `sum_bytes<T>(size$T, p: char*, n: u64): u64` that
  walks an array of `n` elements of size `size$T` and adds up the first
  byte of each element (it uses only the size, as generic code must);
- a function with a `ref` parameter, `incr(ref r: i32)`, adding 1 through
  the pointer;
- the externs `print_i32`, `print_u64`, `print_bool` and `print_string` of
  `Test.c`, whose models append to the world what the C functions print
  (section 11.4).

What it computes and the documented result: `main` prints, in this order,

| printed | from |
| --- | --- |
| `35` | `area(Rect{5, 7})` |
| `27` | `area(Circle(3))` (3·r·r), through a copy of the variant whose unused payload bytes are undefined |
| `6` | `sum3([1, 2, 3])` |
| `42` | `v` after `incr(ref v)` |
| `30` | `arr[0]` after `alloc_array(arr, 3)`, filling with 10, 20, 30 and `swap_elems<i32>(arr, 0, 2)` |
| `3` | `sizeof(arr)` |
| `0` | `sizeof(arr)` after `free_array(arr)` |
| `true` | `print_bool(v > 30 && v == 42)` with short-circuit evaluation |
| `hi` | `print_string(greeting)`, the bytes of the global constant `"hi"`, read through its descriptor (no newline) |
| `142` | `K + v`, with the global constant `K = 100` |

each on its own line except `hi`, and returns 0. The world of the extern
models is the text printed so far, so the lemma `example_run` in
`MiniCExample.thy` checks by `eval` that `run_program` with `le_encoding`
returns `Inr (example_expected, _, MV_Int Signed IntBits_32 0)` where
`example_expected` is exactly that text. `example_prog_wf` checks
`program_wf` and `example_prog_well_typed` checks `program_well_typed` the
same way. A second program, `example_prog_array`, is the same program with
the `bool`-returning `alloc_array` of `packages/coretypes/src/Array.c`
(its result is stored in a `uint8_t` and printed, adding a `true` line after
`42`), with its own `eval` lemmas. Section 11 describes how both are
printed, compiled and run.


## 8. The two target theorems

Written out as they are expected to be stated in stage 5 (typing) and stage
6 (simulation). Names of not-yet-existing definitions: `codegen_module`
(stage 5), `state_rep`, `rep_val`,
`extern_rep`, `hmap` (stage 4), `datatypes_acyclic` (stage 4: every
datatype is non-recursive) and `core_module_sizeable` (stage 4: the static
size bound of section 3.2, which includes acyclicity of the call graph,
together with the facts that every closed type of the program has a byte
size below `2^64` and that the variant tag sizes are as in section 2.3).
The aliasing condition is written as a `RuntimeError` of the proposed Core
check (section 3.4), so it is covered by "normal result".

    theorem codegen_well_typed:
      assumes "core_module_well_typed m"
          and "core_module_closed m"
          and "core_module_ghost_free m"
          and "core_module_flat m"
          and "CM_TypeSubst m = fmempty"            (* normalized *)
          and "datatypes_acyclic (CM_TyEnv m)"
          and "core_module_sizeable m"
          and "fmlookup (CM_Functions m) mainName = Some mainFn"
          and "fmlookup (TE_Functions (CM_TyEnv m)) mainName = Some mainInfo"
          and "FI_TyArgs mainInfo = []" and "FI_TmArgs mainInfo = []"
          and "FI_ReturnType mainInfo = CoreTy_Record []"
          and "codegen_module cnames mainName m = Some prog"
      shows "program_wf prog" and "program_well_typed prog"

    theorem codegen_correct:
      fixes w :: 'w and coreExterns :: "(string, 'w ExternFunc) fmap"
        and minicExterns :: "(string, 'w MExtern) fmap" and enc :: MEncoding
      assumes (the hypotheses of codegen_well_typed)
          and "valid_encoding enc"
          and "hmap 0 = MP_Null" and "inj hmap"
          and "∀f info E. fmlookup (TE_Functions (CM_TyEnv m)) f = Some info
                 ∧ fmlookup coreExterns f = Some E
                 ⟶ extern_fun_contract (CM_TyEnv m) info E
                   ∧ (∃M. fmlookup minicExterns f = Some M
                          ∧ extern_rep (CM_TyEnv m) enc hmap info E M)"
          and "make_interp_state w coreExterns externAlloc m = Inr st"
          and "interp_function_call d fuel st mainName [] [] = Inr (st', v)"
      shows "∃fuel' mem'.
               run_program fuel' enc minicExterns prog w
                 = Inr (IS_World st', mem', MV_Int Signed IntBits_32 0)"

The conclusion says: the MiniC program terminates (some fuel suffices),
never reaches `MErr_UB` (the result is `Inr`; MiniC has no other failure
besides fuel), ends in the same world as the Core run (hence with the same
sequence of extern calls: the world type is universally quantified, so
instantiating `'w` with a trace of calls makes the worlds the traces), and
returns 0. `externAlloc` is arbitrary: Core's allocation oracle only
influences which copies are `RuntimeError`s, and the hypothesis is a normal
result. Non-termination, `TypeError`, `RuntimeError` and
`InsufficientFuel` of the Core run are out of scope, as the task says.


## 9. Risks for stages 4 to 6 and how the design mitigates them

1. **Aliasing between call arguments** (section 3.4). Core and C disagree on
   aliased `ref`/value arguments. Mitigation: the proposed Core runtime
   check, so the condition becomes part of "normal result". Without it the
   theorem needs a hypothesis over the run, which cannot be stated with the
   existing interpreter.
2. **Size overflow in generic code** (section 3.2). The `uint64_t` size
   arithmetic of a generic function could wrap for an instantiation at a
   huge type. Mitigation: the static bound `core_module_sizeable`, checked
   by an executable function over the module and made sound by the stage 4
   lemma that every instantiation a Core run performs respects the bounds.
   That lemma is new Core-side work, but it has one interesting case (the
   call) and needs no instrumentation of the interpreter.
3. **Sharing between const cells and their origins** (sections 3.5, 4). The
   representation relation cannot be a plain injection from cells to
   regions. Mitigation: the "writable locations are unshared" invariant,
   stated above; the alternative (copy by-value aggregates and `Let` values
   into fresh regions) removes region sharing but not heap-block sharing,
   so it would not simplify the invariant and would cost a copy per call.
4. **Undefined payload bytes of variants.** A model that made every read of
   an undefined byte UB would break at the first variant copy. Mitigation:
   `MB_Undef` is copyable; only decoding is UB; the relation's `junk`.
   Since stage 3b the generated code zeroes variant buffers (section 3.3),
   so generated programs never copy undefined bytes and `junk` is in fact
   zero; the relation keeps `junk` arbitrary because that is simpler and
   still sound, and `undef_copy_prog` in `MiniCExample.thy` keeps the
   semantics' tolerance of undefined bytes exercised.
5. **Lazy references** (section 3.5). The generator's environment, not
   MiniC, carries them; the proof must relate a Core `(addr, path)` to a
   recomputed address. Mitigation: freeze indices as Core does; the path
   resolution lemma is the same one `Assign` needs.
6. **Fuel.** Core and MiniC fuel are unrelated. Mitigation: the theorem is
   existential in MiniC fuel; `MiniCFuelMono.thy` gives monotonicity, and
   the simulation lemmas are stated as "for some fuel", combined with
   monotonicity when composing.
7. **Extern hypothesis strength** (section 6.2). Too weak and the array
   lemmas fail (e.g. without the frame condition a `print` could clobber a
   local); too strong and `Array.c` does not satisfy it (e.g. requiring
   `calloc(0, n)` to return null). Mitigation: the sketch keeps the
   zero-element case unconstrained and demands only a frame condition and
   representation of the results; the comparison of section 11.4 against
   the real `Array.c`/`Test.c` is the sanity check (both allocation
   conventions, `Test.c`'s `void` one and `Array.c`'s `bool` one, run
   correctly against the models of `MiniCExample.thy`).
8. **Integer promotion and `int` width.** Mitigation: MiniC arithmetic is
   mathematical with a fits check, Core guarantees the fit, and the only
   promotion-sensitive operations (shifts) go through the helpers of
   section 5.3 under A2/A5.
9. **Default values are all-zero bytes.** The `Default` lowering relies on
   it. Mitigation: `valid_encoding` has the zero law, `encode_ptr` null is
   zero bytes, and stage 4 proves `default_value_rep_zero` by induction over
   the type (fuelled as `default_value` is).
10. **Datatype and call-graph acyclicity / sizes.** `size` of a recursive
    datatype would not terminate, and the size bound of section 3.2 needs
    a topological order of the functions. Mitigation: `datatypes_acyclic`
    hypothesis, and the `core_module_sizeable` checker computes the
    function order itself and fails on a cycle. The elaborator already
    rejects recursive functions (`check_sccs`) and should reject recursive
    datatypes too (to be confirmed in stage 4); either way the pipeline
    runs the checks, so no elaborator proof is needed.
11. **The printer** is unverified; precedence, integer literal syntax
    (`INT64_MIN`), integer promotion, the shift helpers, the mangling and
    the aliasing obligation P1 of section 5.2 are all places for silent
    errors. Printing `ME_Load`/`MS_Store` as typed dereferences instead of
    `memcpy` would make nearly every generated function violate C99 6.5p7
    (every field read comes out of a `char` buffer), which gcc at `-O2`
    does exploit, while leaving the Isabelle side unchanged. Mitigation
    (section 11.2): the MiniC AST is small and the printer parenthesises
    everything, casts every arithmetic result to its MiniC type, prints
    every literal with its type's macro, and implements P1 by helper
    functions, so each rule is one line of `MiniCPrint.thy`; the examples
    are compiled with `-Wall -Wextra -pedantic -Werror` at `-O0` and `-O2`
    under three standards and compared with the interpreter byte for byte
    (section 11.4); from stage 5 on the codegen tests in
    `test/cases/codegen` are an independent oracle. Known gaps are listed
    in section 11.2 (reserved identifiers) and 11.3.
12. **Zero-sized aggregates** (`{}`, `T[0]`). C forbids zero-length arrays.
    Mitigation: every buffer declaration uses `max 1 |ty|`; copies of 0
    bytes are fine; the unit type is `void` in signatures.
13. **Evaluation of `CoreTm_Var` for a `ref` with an invalid path** (e.g. a
    re-tagged variant) is a `RuntimeError` in Core, so excluded; but the
    proof must show the generated load is then never executed, which it is,
    because the lowering reads through the pointer exactly where Core
    resolves the path.
14. **Extern handles.** `hmap` must be a single injection for the whole run,
    so an extern cannot "return the same handle as a different pointer".
    Mitigation: `hmap` is a parameter of the theorem, shared by all
    `extern_rep` instances.


## 10. Proposals for changes outside this directory (for stage 4 or 5)

- `CoreInterp`: the argument aliasing check (section 3.4).
- `elab_program`/driver: return the extern C-name map (section 3.9).
- `CodeExport`/the driver: run the `core_module_sizeable` checker of
  section 3.2 (and `datatypes_acyclic`, if it is not a consequence of
  elaboration) on the module before code generation. The size bound is a
  property of the program's instantiations, not of elaboration, so it has
  to be checked; it cannot fail on realistic programs.
- If stage 5 wants to run generated MiniC programs in the Haskell driver
  (as an oracle next to the C output), the interpreter needs code equations
  without `Suc` on the left-hand side: `CodeExport.thy` uses
  `Code_Binary_Nat`, whose `Suc`-elimination preprocessor handles one `Suc`
  equation per `f 0` equation, and `exec_stmt` and friends match on the
  fuel *and* on the statement. One `[code]` lemma per equation of the form
  `exec_stmt fuel ctx st s = (if fuel = 0 then Inl MErr_Fuel else ...)`,
  proved by `cases fuel`, would do it; nothing in stage 3b needs it, so the
  driver exports the documented expected output instead (section 11.4).


## 11. The printer and the C-level validation (stage 3b)

### 11.1 Building, printing, compiling, running

From `isabelle/`, the full build with export (it checks every theory,
including the `eval` of the examples, and writes the Haskell code):

    isabelle export -d. -x 'Babylon.CodeExport:code/**' Babylon
    cd export/Babylon.CodeExport/code/export1 && cp ../../../../Main.hs . && ghc -O Main.hs

Then, from the root of the repository:

    ./isabelle/minic/check_example.sh            # all examples
    ./isabelle/minic/check_example.sh example    # one of them

The script runs, for each example `NAME` in `minic_examples`
(`MiniCExample.thy`):

    isabelle/export/Babylon.CodeExport/code/export1/Main --minic NAME NAME.c NAME.expected

which writes the printed C to `NAME.c` and the stdout that the MiniC
interpreter computes for the program (the world of the extern models,
section 11.4) to `NAME.expected`; compiles `NAME.c` with
`gcc -std=c99 -Wall -Wextra -pedantic -Werror`, and again with `-std=c11`
and `-std=c17`, each at `-O0` and `-O2`; links it; runs it; and compares
the output and the exit status (0) with the interpreter's. The files are
left in `$TMPDIR/minic-check` (default `/tmp/minic-check`) for inspection.
Nothing in `test/isabelle_test.sh` exercises MiniC; this script is the
MiniC check.

Linking: `example` is linked against `test/test-support-0.1/src/Test.c`
(the `print_*` functions and the always-succeeding `void alloc_array`,
`void free_array` that `test/test-support-0.1/src/Test.b` declares);
`example_array` is the same program calling `packages/coretypes/src/Array.c`'s
`bool alloc_array` instead, linked against `Array.c` plus `Test.c` compiled
with its `alloc_*_array` and `free_*_array` functions renamed by `-D`
macros (`-Dalloc_array=test_alloc_array` and so on), because the two files
define the same symbols with different prototypes and cannot be linked
together as they are. (A real program imports either `Test` or `Array`,
never both.)

### 11.2 What the printer emits

`print_program` (`MiniCPrint.thy`) is a plain traversal of the syntax. The
generated file is, in order: a comment; `#include <limits.h>`, `<stdint.h>`,
`<string.h>`; `#error` guards for A1 (`CHAR_BIT != 8`), A2
(`(-1 & 3) != 3`, which holds only in two's complement) and A5
(`(-1 >> 1) != -1`); the helper functions; the globals; one prototype per
function (so that definition order is irrelevant); the function
definitions. Conventions:

- **Types.** `CTy_Int s b` is `int8_t` ... `uint64_t`; `CTy_CharPtr` is
  `char *`; `CTy_VoidPtr` is `void *`. A void function is `void`; `main` is
  printed as `int main(void)` whatever its `MF_Ret` (`-Wmain` would
  complain about `int32_t main`); a function without parameters is `f(void)`.
- **Expressions are fully parenthesised**, so precedence never matters.
- **Every arithmetic result is cast back to its MiniC type**:
  `((int32_t) ((a) + (b)))`, `((uint8_t) (~(x)))`, `((uint8_t) ((a) < (b)))`,
  `((uint8_t) (!(e)))`. The cast undoes C's integer promotions; without it
  `~x` on a `uint8_t` is a negative `int`, and `x == 255` would then be
  false. For a value that fits the type the cast is exact, so under the
  MiniC precondition (the result fits) C computes the same value. The
  printer gets the type from `expr_type`, for which it threads the typing
  environment through the statements exactly as `stmts_ok` does; if an
  expression is ill-typed the cast is simply omitted.
- **P1 (no typed access through a pointer):** `ME_Load ty p` is
  `bab_load_<ty>(p)` and `MS_Store ty p e` is `bab_store_<ty>(p, e)`, where
  the helpers are `static inline` functions doing a `memcpy` of `sizeof v`
  bytes into or out of a local `v` of type `ty` (`<ty>` is `i8` ... `u64`,
  `cp` for `char *`, `vp` for `void *`). `MS_Copy` is `memmove`, `MS_Zero`
  is `memset(p, 0, n)`. `ME_AddrOf x` is `((char *) &x)` for a scalar and
  `x` for a buffer (which decays to `char *`); `ME_PtrAdd p i` is
  `(((char *) (p)) + (i))`, the cast making it valid for a `void *` operand
  too. `ME_PtrSize` is `((uint64_t) sizeof(void *))`. All helpers are
  emitted in every file; `static inline` keeps the unused ones from
  triggering `-Wunused-function`.
- **Shifts** are the helpers `bab_shl_<ty>`/`bab_shr_<ty>` of section 5.3
  (the idiom of `shift_binop` in `codegen.c`), taking the count as a
  `uint64_t`. **`CB_Max`** is the helper `bab_max_<ty>`, except at file
  scope, in the size of a global buffer, where no call is allowed in a
  constant expression and it is printed as `((a) > (b) ? (a) : (b))`.
- **Literals** use the `INTn_C`/`UINTn_C` macros of `<stdint.h>`:
  `INT32_C(5)`, `(-INT32_C(5))`, and `((-INT64_C(9223372036854775807)) - 1)`
  for the most negative value of a signed type, whose magnitude does not
  fit the type (the same three cases as `codegen_int_literal` in
  `codegen.c`).
- **Statements.** `T x;` and `char x[n];` (a VLA when `n` is not constant)
  for declarations; `x = e;`; `if (c) { ... } else { ... }` (no `else` when
  the else branch is empty); `while (1) { ... }`; `break;`; `{ ... }`;
  `f(args);` or `x = f(args);`; `return;` or `return e;`. Every `if` branch,
  loop body and block is a compound statement, i.e. a C scope, matching
  `exec_scope`.
- **Globals** are file-scope variables with no initialiser (`int32_t K;`,
  `char greeting[((uint64_t) sizeof(void *)) + 8];`), so static storage
  zero-fills them, as `alloc_globals` does; the generated `main` stores the
  initial values (section 3.7). Globals and functions are not `static`
  (an unused `static` object would warn under `-Wall`).
- **Names** are mangled as `mangle_name` in `codegen.c` and
  `docs/c-interface.md` ("Calling Babylon Functions from C"): `.` to `z_`,
  `/` to `zs`, `@` to `za`, `^` to `zh`, `-` to `zm`, `z` to `zz`, a leading
  `_` to `zu`; and, beyond `codegen.c` (which rejects any other character),
  any other character to `zx` followed by two hex digits, so that names such
  as the generator's temporaries can contain `$`. A name that comes out equal
  to a C keyword (C99, C11 and C23), one of `memcpy`, `memmove`, `memset`,
  `size_t`, `NULL`, `CHAR_BIT`, the `<stdint.h>` type and `INTn_C` macro
  names, or one of the helper names gets a `z` appended (as `codegen.c` does
  for its own list). Extern functions are printed under their C name
  (`MF_Extern = Some cname`), unmangled, both in the prototype and at each
  call; the prototype has the form of `docs/c-interface.md` because the
  parameter list of an extern `MFun` already does (section 3.9).
- **Reserved identifiers.** Mangled names never start with `_`, so they do
  not collide with the identifiers C reserves. Two residual risks, shared
  with `codegen.c`: a mangled name can collide with a macro of an included
  header (`INT32_MAX`, ...) or with a C library function (`free`, `abort`)
  if the MiniC name is unqualified, which only the hand-written examples
  have (generated functions and globals are qualified `Mod.name`; locals
  are not, and a local named `abort` would shadow the library function
  harmlessly unless the same function also calls an extern of that C
  name); and the `z` suffix makes mangling non-injective in the one case
  of a name that is itself a reserved name plus `z` (`intz`). The typing
  judgement rules out MiniC-level collisions between variables and
  functions, and the collisions above are not MiniC-level, so they are
  outside the theorems; stage 5 should keep temporaries' names
  unmangleable into anything reserved (a `$` in every temporary does it).

### 11.3 What the printer relies on

- The prototype mismatches that `Test.c` has always had with the
  `docs/c-interface.md` prototypes and that `codegen.c`'s output relies on:
  `print_bool` is declared `void print_bool(uint8_t)` in the generated file
  and defined `void print_bool(bool)` in `Test.c`, and `print_string` is
  declared with `char *` and defined with `void *`. These are compatible on
  every mainstream ABI (both are passed the same way), which is a property
  of `Test.c` rather than of the printer; `Array.c` uses `char *` and
  `uint64_t` exactly as prescribed. A C name of an extern is just a string
  and the printer has no way to check it against anything.
- `-pedantic` is clean: the printed code uses no extension (the only
  construct that would be one, `void *` arithmetic, is avoided by the cast
  in `ME_PtrAdd`).
- `-Wreturn-type` (in `-Wall`) warns about a non-void function whose body
  can fall off the end. The generator (section 3.6) need not end every body
  with a `return`, because Core raises `RuntimeError` there; such a program
  would print with a warning. The example's functions all end in `return`.

### 11.4 The validation and what it found

The extern models of `MiniCExample.thy` have the *text printed so far* as
their world (it was a list of integers in stage 3a): `print_i32`/`print_u64`
append the decimal number and a newline, `print_bool` appends `true` or
`false` and a newline, `print_string` appends the bytes of the string up to
its null terminator (no newline), exactly as `Test.c` writes them. So the
interpreter's final world *is* the expected stdout, `example_expected`, and
the driver writes it to `NAME.expected` for a byte-for-byte comparison.
The `eval` lemma `example_run` checks the interpreter against it, and
`example_prog_well_typed` checks the typing judgement, both by `eval`.

Outcome (gcc 13.3, x86-64 Linux, glibc with `_FORTIFY_SOURCE` on by
default at `-O2`): both examples compile without a warning under
`-std=c99`, `-std=c11` and `-std=c17`, at `-O0` and `-O2`, with
`-Wall -Wextra -pedantic -Werror`, link against `Test.c` (and `Array.c`),
return 0 and print exactly `example_expected` and `example_array_expected`.
Two things were found and fixed on the way:

1. **The driver cannot run the interpreter.** `CodeExport.thy` uses
   `Code_Binary_Nat`, and the interpreter's equations match on `Suc fuel`
   together with the statement, which its `Suc`-elimination preprocessor
   does not handle (section 10). The driver therefore writes the documented
   expected text, and the `eval` lemmas are what tie it to the interpreter.
   No change to the semantics.
2. **`memmove` of a partially initialised buffer.** The stage 3a example
   built `Circle(3)` leaving the four bytes after the payload undefined (as
   `codegen_variant` does) and then copied the variant. That is valid C
   (the object's address is taken and `char` has no trap representation),
   and the semantics defines it (section 2.1), but gcc 13's
   `-Wuninitialized` reports `'sh2' is used uninitialized` at `-O2` when
   `memmove` is glibc's fortified inline wrapper (the warning disappears
   with `-D_FORTIFY_SOURCE=0`). Rather than have every generated variant
   construction warn on a default Ubuntu toolchain, the lowering of
   `VariantCtor` now zeroes the buffer first (section 3.3) and the example
   does the same; `undef_copy_prog` keeps the semantics' handling of
   undefined bytes checked in the interpreter. No change to the semantics
   or the memory model.

Not a finding, but confirmed: the `print_bool`/`print_string` prototype
mismatches of `Test.c` (section 11.3) are harmless on this ABI, as they
have always been for `codegen.c`'s output.
