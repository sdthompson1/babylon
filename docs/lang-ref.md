
# Babylon v0.1 Language Reference

Stephen Thompson, January 2025

This is the reference manual for version 0.1 of the "Babylon"
programming language. It describes the syntax and semantics of the
language.

# Introduction

Babylon is an imperative programming language designed to support
"verification" features. This means that the programmer is able to
state certain properties, such as function preconditions and
postconditions, that they expect their program to satisfy; the
language then provides facilities for verifying, at compile time, that
the program does indeed have these properties.

Consequently, programs written in Babylon should (in theory) have a
higher degree of robustness and reliability than is commonly found in
today's software industry. For example, (again, in theory) it should
be impossible for a verified Babylon program to encounter any kind of
"crash", such as a division by zero error, memory access fault and so
on, at runtime (although this applies only to the Babylon code; if the
program is linked with libraries written in other languages, then
those libraries might still cause a crash, of course).

Currently, a prototype compiler for Babylon is available from
https://github.com/sdthompson1/babylon. The compiler has two modes:
"verify" mode, which uses external SMT solvers (such as z3, cvc5 and
vampire) to verify the correctness properties of the program; and
"compile" mode, which compiles the program to an executable file
(currently this is done by translating the Babylon program to C, and
then using a C compiler).


## Purpose of this document

The aim of this document is to give a description of the syntax and
semantics of the Babylon language, as it currently stands (at version
0.1).

The aim is not to give a completely precise and formal definition of
the language; rather, we are just trying to document and describe the
language as best we can at this time. Some minor details may be
missing or incorrect, but the author hopes that nothing important has
been left out, at least.

In future, the author hopes to create a more rigorous definition of
the language, perhaps in a similar style to "The Definition of
Standard ML" (by Robin Milner et al), or perhaps a formally verified
definition written in something like Isabelle or Coq. It will probably
be a long time before this actually happens though.


## Related work

One existing language that is quite similar to Babylon in spirit is
Dafny (https://dafny.org/) by Microsoft Research. One difference is
that while Babylon aims to keep the language as simple and "low-level"
as possible, Dafny embraces more complex features; for example, Dafny
uses garbage collection, while Babylon relies on manual memory
management; and Dafny includes a number of features, like "traits" and
higher-order functions, which are missing from Babylon.

SPARK (https://en.wikipedia.org/wiki/SPARK_(programming_language)) is
another well-known language that allows for formal verification. SPARK
actually has very similar design goals to Babylon, including simple
and unambiguous semantics, bounded resource requirements, and minimal
runtime system requirements. SPARK has also been around for a long
time, and has been used successfully in many industrial applications,
while Babylon is only a prototype at present. One area of difference
is that Babylon has a more modern syntax, similar to C or Rust, while
SPARK is based on Ada, which may appear unfamiliar to programmers who
are used to more recent languages.


## Future plans

As mentioned, the Babylon language and compiler are currently at a
prototype stage. Ideally the author would like to make the following
improvements:

- Creating a more robust compiler implementation (perhaps even a
  formally verified implementation in something like Isabelle). This
  would give users more confidence that the compiled code does indeed
  have the properties that the verifier claims it does (although the
  users would still have to trust any SMT solvers used, of course).

- Extending the Babylon language itself. Although the intention is to
  try to keep the language as simple as possible, there are
  nevertheless some things that do need to be added, such as
  recursion. (Currently the language supports neither recursive
  functions nor recursive datatypes, which means that even something
  as simple as a linked list cannot currently be implemented, at least
  not without resorting to external C code.)


# Overall Structure

At a high level, the structure of a Babylon program is as follows.

A Babylon program consists of one or more *modules*. Each module is
represented by its own source code file on disk. A module consists of
zero or more *declarations*. Declarations represent the individual
elements of a program, such as types, functions and constants. Each
declaration has a *name*, and each declaration may or may not be
*exported* by the module.

Modules can also *import* other modules. Importing a module means that
the importing module is able to access and refer to any of the
*exported* declarations from the imported module (but not the
*non-exported* declarations, which are considered private to that
module). For example, if an `Algorithms` module exported a function
called `sort`, then any importer of `Algorithms` would be able to call
the `sort` function.

Declarations in general can be referred to by either their *qualified*
or *unqualified* name. Continuing the above example, the unqualified
name of the "sort" function would be `sort`, but the qualified name
would be `Algorithms.sort` (i.e. the module name, followed by a dot,
followed by the declaration name). Generally, the unqualified name is
shorter and more convenient to use, but if two different modules
export an entity with the same name, then it becomes necessary to use
the qualified name, in order to disambiguate between them.

Declarations are themselves built out of simpler elements such as
*expressions*, *statements* and *types*. For example, a `const`
declaration may specify that it has type `i32` (32-bit signed integer)
and value `1 + 2` (an expression). A `function` declaration will
specify (among other things) a list of program statements to be
executed when the function is called.

At the lowest level, we find that each of the above entities is
represented as a sequence of *tokens*, such as individual identifiers,
numeric constants, or punctuation or operator symbols. This is known
as the *lexical structure* of the language.

We will now go on to describe each of these elements in a bottom-up
fashion.


# Lexical Syntax

Each Babylon source code file is, ultimately, a finite sequence of
bytes (i.e. integer values between 0 and 255 inclusive). The purpose
of this section is to describe how these bytes are interpreted and how
they end up being assembled into a sequence of *tokens*. (Later
sections will describe how these tokens combine to create larger
units, such as statements, declarations, or entire modules.)

For the most part, the bytes are interpreted as ASCII text (and
therefore must be valid ASCII character codes). An exception is made
for string and character literals, which may include arbitrary bytes,
either directly or via escape sequences (the interpretation of these
bytes is up to the individual program; no particular character set is
imposed by the language). A further exception is made for comments,
which are allowed to include arbitrary non-ASCII bytes if the
programmer wishes (since the language ignores the contents of comments
anyway, this will make no difference to the program's meaning).

In general, if a file has been parsed into tokens up to a certain
point, then the next token is the longest sequence of characters that
would constitute a valid token (after skipping any whitespace
characters). For example, if the next characters are `abc123+`, then
the next token would be `abc123` (not `abc`) and then parsing would
resume from the `+` character. If however the next characters were
`abc 123 +`, then the next token would be `abc` and then parsing would
resume from the `1` character (skipping the whitespace).

Note that in the above, "whitespace" refers to ASCII characters in the
range 9--13 or 32 (that is, the tab, newline, vertical tab, form-feed,
carriage return, or space characters).

We are now ready to list the valid tokens that form part of the
language, which are as follows:

- Keywords: any word from the following list is considered a keyword:

   - `allocated`, `assert`, `assume`, `bool`, `case`, `cast`, `const`,
     `datatype`, `decreases`, `else`, `ensures`, `exists`, `extern`,
     `false`, `fix`, `forall`, `function`, `ghost`, `hide`,
     `i8`, `i16`, `i32`, `i64`, `if`, `import`, `impure`, `in`, `int`,
     `interface`, `invariant`, `let`, `match`, `module`, `obtain`,
     `old`, `real`, `ref`, `requires`, `return`, `show`, `sizeof`,
     `swap`, `then`, `true`, `type`, `u8`, `u16`, `u32`, `u64`, `use`,
     `var`, `while`, `with`.

- Identifiers: Any sequence of alphanumeric characters (`A` to `Z`,
  `a` to `z`, or `0` to `9`) or underscores (`_`), not beginning with
  a numeric digit, and that is neither a keyword nor a lone
  underscore, is considered an identifier. Identifiers are used to
  refer to variables, functions and other entities.

- Integer literals: Any consecutive sequence of the digits `0` to `9`,
  optionally preceded by a minus sign (`-`), is considered an integer
  literal written in decimal format. Hexadecimal literals are also
  allowed; these consist of the sequence `0x` (or `0X`) followed by
  one or more valid hex digits (`0` to `9`, `a` to `f`, or `A` to
  `F`). (Negative hex literals are not supported.)

- String literals: A sequence of non-`"` characters enclosed within a
  pair of `"`s is a string literal. For example, `"hello"`. It is an
  error if a newline character (ASCII 10) occurs within a string
  literal, or if the file ends before the second `"` is encountered.
  Also, the backslash (`\`) character may be used within string
  literals to create "escape sequences". These have the following
  meanings:
   - `\a` represents the alert/bell character (ASCII 7).
   - `\b` represents a backspace (ASCII 8).
   - `\f` represents a form-feed (ASCII 12).
   - `\n` represents a newline (ASCII 10).
   - `\r` represents carriage return (ASCII 13).
   - `\t` represents a tab (ASCII 9).
   - `\v` represents vertical tab (ASCII 11).
   - `\"` represents a double quote character (ASCII 34); the `"` is
     not intepreted as ending the string in this case.
   - `\'` represents a single quote character (ASCII 39).
   - `\\` represents a backslash. (This is how you can write actual
     backslash characters within a string literal.)
   - `\x00`, where the 0's may be any valid hex digit (0-9, A-F or
     a-f), represent the byte given by the corresponding hex code
     (interpreted as an unsigned 8-bit number).
   - Any other character following the backslash is an error.

- Character literals: A single quote (`'`) followed by a single
  character (or one of the above backslash-escape sequences) followed
  by another `'` is a character literal. This is the same as if the
  number corresponding to the ASCII code of the character (or the
  number resulting from the escape sequence) had been entered directly
  as an integer literal. For example, `'A'` is considered to represent
  the same token as `65`, and `'\t'` is considered the same as `9`.

- Operators and punctuation: `+`, `-`, `*`, `/`, `%`, `&`, `&&`, `|`,
  `||`, `^`, `!`, `~`, `<`, `<<`, `<=`, `<==`, `<==>`, `>`, `>>`,
  `>=`, `=`, `=>`, `==`, `==>`, `!=`, `:`, `;`, `,`, `.`, `(`, `)`,
  `{`, `}`, `[`, `]` and `_` are all valid tokens, representing
  various operators or pieces of punctuation. (Their precise meanings
  will be described below.)

- Comments: The token `/*` begins a block comment. Any
  characters/bytes up to including the following `*/` are ignored.
  Block comments may also be nested. Meanwhile, the token `//` begins
  a single-line comment; any characters/bytes upto and including the
  next newline (ASCII code 10) are ignored.



# Types

The language includes the following types:

 - `bool`: Boolean type, which has two possible values: `true` and
   `false`.

 - `u8`, `u16`, `u32`, `u64`: Unsigned integer types, of 8, 16, 32 and
   64 bits respectively. An N-bit unsigned type holds an integer
   between 0 and 2**N - 1, inclusive (where "**" represents
   exponentiation).

 - `i8`, `i16`, `i32`, `i64`: Signed integer types, of 8, 16, 32 and
   64 bits respectively. An N-bit signed type holds an integer between
   -2**(N-1) and 2**(N-1) - 1, inclusive (where "**" represents
   exponentiation).

 - Mathematical types: `int` represents the type of (unbounded)
   integers, and `real` represents the type of real numbers. Note that
   these are not supported for use in executable code; they are usable
   only in verification contexts.

 - Tuple types: if `T1`, ..., `Tn` are types, then `{T1, ..., Tn}` is
   a tuple consisting of fields of those types. For example, `{i32,
   bool, u8}` is a valid tuple type. The fields are numbered starting
   from zero. Note that empty tuples and single-field tuples are
   allowed, so e.g. `{}` and `{i16}` are valid tuple types. Tuples can
   also be nested, e.g. `{{i32,i8},bool}` is a valid tuple type.

 - Record types: These are similar to tuples except that the fields
   are named (field names must be valid identifiers). The syntax is
   `{fieldname: type, ...}`, e.g. `{red: u8, green: u8, blue: u8}` is
   a valid record type. Note that fields are ordered, so e.g. `{green:
   u8, blue: u8, red: u8}` is a different record type from the above.
   Also, single-field record types (such as `{flag: bool}`) are
   permitted, but not empty record types, because `{}` technically
   represents an empty tuple rather than an empty record.

 - Array types: These are divided into three categories:

    - Fixed-sized arrays: If `T` is a type, then `T[n]` is an array of
      `n` consecutive values of type `T`. Here, `n` can be any
      constant expression (i.e. an expression whose value is known at
      compile time) of type `u64`. For example, `i32[10]` is an array
      of ten `i32` values. Multi-dimensional arrays are also
      supported, e.g. `bool[10,20]` (a 2-d array of bools) or
      `{i8,i8}[10,20,30]` (a 3-d array of tuples).

    - Allocatable arrays: If `T` is a type then `T[*]` is a
      one-dimensional allocatable array of `T` values. An allocatable
      array starts off "empty" (i.e. containing zero elements), but it
      can be "resized" later at runtime (by allocating heap memory).
      Multi-dimensional allocatable arrays are also supported, e.g.
      `i32[*,*,*]` is a three-dimensional array of 32-bit signed
      integers, which can be dynamically resized at runtime (available
      heap memory permitting). Note also that arrays must be either
      fully allocatable, or fully fixed-size; e.g. `u8[*, 10]` is
      illegal.

    - Incomplete arrays: An array type like `T[]` or `T[,,]` is called
      an "incomplete" array type. Incomplete array types can only
      appear as the types of function parameters (e.g. you cannot
      declare a variable of an incomplete type). An incomplete type
      means that the function might receive *either* a fixed-size *or*
      an allocatable array as a parameter. This means that the
      function must treat the array size as known only at runtime
      (similar to an allocatable array) but the function also cannot
      resize the array dynamically (similar to a fixed-sized array).

 - Named types: any valid identifier, e.g. `MyType`, can also be used
   as a type. Typically this will be used to refer to a type created
   in a `typedef` or `datatype` declaration (see below), or else to a
   type variable appearing in a generic declaration (such as a
   generic `function` -- again, see below for details).



# Expressions

The following kinds of expressions are supported.

## Variables

A single identifier, such as `x`, may be used as an expression. It
refers to the value of the variable `x`, which itself may have been
declared in a variable declaration statement, or as a function
parameter, or it may be a global constant declared in a `const`
declaration. It could also refer to a function (if the "variable
expression" happens to be the left-hand side of a function call
expression).

Note the scoping rules that apply. Consider the expression `x`. If
there is a local variable (or a function parameter) named `x` in
scope, then the expression refers to that variable. (If there are
multiple `x`s in overlapping scopes, then the expression refers to the
variable from the "innermost" scope; any `x`s from "outer" scopes are
shadowed.) Otherwise, if the current module declares a function or
constant named `x`, then the expression refers to that function or
constant. Otherwise, we must look at the imported modules (and in
particular, "unqualified" imports, i.e. those that use `import` rather
than `import qualified`). If exactly one of those modules exports a
function or constant named `x`, then the expression resolves to that.
Otherwise, the expression `x` is an error (an "ambiguity" error if
multiple different `x`s were found, or a "not in scope" error
otherwise).

Note also that functions/constant names, and type names, are
considered to be in two separate "namespaces". Therefore, if the
identifier `x` is found in an expression context, it can never refer
to a datatype or typedef named `x`; it can only refer to a function,
constant, or local variable (including function parameters), as
described above.


## Literals

The keywords `true` and `false` represent constants of type `bool`.

An integer literal (such as `123` or `-456` or `0xabcd`) represents a
constant of type either `i32`, `u32`, `i64` or `u64`. The type chosen
is the first type from that list for which the integer constant is a
legal value of that type. For example, `123` has type `i32`, because
`123` is a legal `i32` value. But `3000000000` has type `u32`, because
this value is outside the `i32` range, but inside the `u32` range.
Similarly, `-3000000000` has type `i64`, because this value is not a
valid `i32` nor `u32` value, but is a valid `i64` value.

If an integer literal is not in the valid range of any of the four
types mentioned above, then it is an error.

Note also that hex literals are treated as unsigned, so e.g.
`0xffffffff` is considered equal to `4294967295` (of type `u32`), and
not, for example, `-1` of type `i32`.

Character constant literals are treated in the same way as integer
literals; so, for example, the expression `'A'` has type `i32` and
value 65.

A string literal (such as `"hello"`) is considered to have type
`u8[N]`, where N is the number of bytes in the string, plus one. The
string literal refers to a read-only, statically allocated array,
whose contents are the bytes of the string literal, plus a final zero
("null") byte. For example, the string literal `"hello"` represents a
`u8[6]` array containing the values 104, 101, 108, 108, 111 and 0 (the
ASCII codes of the letters in "hello", plus a final zero).

Array literals are also supported. An array literal is a
comma-separated list of expressions, enclosed in square brackets. For
example, `[1, 2, 3]` is an array literal. The expressions must be
constant (i.e. their value must be known at compile time) and all of
the same type. The array literal then has type `T[N]` where `T` is the
type of each of the expressions, and `N` is the number of such
expressions listed. For example, `[1, 2, 3]` has type `i32[3]`.
Similarly to string literals, array literals refer to a statically
allocated, read-only piece of memory, containing the relevant array.


## Unary operators

There are three supported unary operators: negation (`-`), bitwise
complement (`~`), and logical not (`!`).

The expression `- E` (where E is another expression) computes the
negative of E, where E must have one of the types `i8`, `i16`, `i32`,
`i64`, `int` or `real`. (The result of the negation has the same type
as E itself.) The verifier will try to prove that the result of the
negation lies within the range of the relevant type (if this proof
fails, then a verifier error results).

The expression `~ E` represents the bitwise complement of E. This is
only valid for the types `i8`, `i16`, `i32, `i64`, `u8`, `u16`, `u32`
and `u64`. In the case of the signed types, "twos complement"
representation is assumed. No verification checks are required as the
result of this operation will always be a valid value for its type.

The expression `! E` represents the logical negation of a boolean
value. E must have type `bool` and the result has type `bool`. Again,
no verification checks are required.


## Binary operators

The language includes the following binary operators, which are parsed
in the following order of precedence:

 - `*` `/` `%` `&` `<<` `>>`
 - `+` `-` `|` `^`
 - `>` `>=` `<` `<=` `==` `!=`
 - `&&`
 - `||`
 - `==>` `<==`
 - `<==>`

Operators nearer the top of this list have higher precedence than
those below, e.g. `1 + 2 * 3` is parsed as `1 + (2 * 3)` rather than
`(1 + 2) * 3`.

Except as noted below, all operators are left-associative. For
example, `1 - 2 - 3` is parsed as `(1 - 2) - 3`, rather than `1 - (2 -
3)`.

We now describe each of the binary operators in turn.

The expressions `E + E`, `E - E`, `E * E`, `E / E` and `E % E` are
supported for all of the numeric types (`i8`, `i16`, `i32`, `i64`,
`u8`, `u16`, `u32`, `u64`, `int` and `real`) -- with the exception of
the `%` operator which does not work for `real` operands. These
calculate addition, subtraction, multiplication, division and "modulo"
(remainder after division) in the usual way.

In the case of integer division, `/` and `%` implement so-called
"truncating" division; this means that `a / b` is defined to be the
integer part of the rational number a/b (i.e. rounding towards zero if
necessary), and `a % b` is defined such that the equation `a == (a /
b) * b + (a % b)` is satisfied.

If the two input operands do not have the same type, then implicit
type conversion is applied as follows:

 - If one of the types is `int` or `real` then a type error results.

 - Otherwise, both inputs are implicitly cast to the first type from
   the following list which is capable of holding all possible values
   of both of the input types: `u8`, `u16`, `u32`, `u64`, `i8`, `i16`,
   `i32`, `i64`. (For example, in `a + b` where `a` has type `i16` and
   `b` has type `u32`, both `a` and `b` will be implicitly cast to
   `i64` since this is the smallest type that can hold all possible
   `i16` and `u32` values.)

 - Alternatively, if the previous step is not possible (which happens
   when the input types are `i64` and `u64`), then both inputs are
   implicitly cast to `u64`. (In this case, the verifier will check
   that the `i64` input is non-negative; if this cannot be proved,
   then a verifier error results.)

The result of the operation will then have the same type as the two
input operands (which now both have the same type, following the above
procedure).

If applicable, the verifier checks that the result of the operation
does not overflow the range of the relevant type. For example, in `x +
y`, if `x` and `y` are both of type `i32`, then the result is also
`i32`, and so the verifier will try to prove that the actual runtime
value of `x + y` is within the range of an `i32`; if this is not
provable, then a verifier error will result. Note that this check is
*not* required for `int` and `real`, since those types have infinite
range, but it is (usually) required for the finite-sized integer
types.

In addition, for the division operations (`/` and `%`), the verifier
will try to prove that the right-hand side (the divisor) is non-zero;
if this proof fails, verification will not succeed.

The following bitwise logical operators are also supported: `&`, `|`
and `^`. Like in C, these represent bitwise "and", "or" and "xor"
respectively. These work on the finite-sized integer types (`i8`
through `i64` and `u8` through `u64`) only. In the case of the signed
types, twos complement representation is assumed. No verification
checks are required for these operations. The same implicit casting
rules as for the arithmetic operators (outlined above) apply.

Bit-shift operations (`<<` and `>>`) are also supported. In this case,
both operands have to be finite-sized integers (`i8` through `i64` or
`u8` through `u64`) but they do not necessarily have to be the same
type; no implicit casting is done. The verification conditions are
that the right-hand operand has to be between 0, and the number of
bits in the type minus one, inclusive; and that the result of the
shift (in the case of left shifts) must not overflow. The semantics
are that left shifting is equivalent to multiplying the left-hand
operand by 2 to the power of the right-hand operand; and right
shifting is equivalent to dividing by 2 to the power of the right-hand
operand, rounding down (note this is different from the `/` operator
which rounds towards zero). This means that `>>` is an arithmetic
shift when used with a signed left-hand operand, or a logical shift
when used with an unsigned left-hand operand.

Equality and inequality can be tested using the `==` and `!=`
operators. In executable code, there is a restriction that the
operands of `==` and `!=` have to be `bool` or numeric types (`i8`
through `i64` or `u8` through `u64`); in non-executable code, any
types are permitted (except that the operands are not allowed to be
functions). Implicit casting may be applied to the operands, just as
for the arithmetic operators (see above). The result of the operation
has type `bool`, and evaluates to `true` if the two operands have the
same value (for `==`) or a different value (for `!=`), or `false`
otherwise. Note that the comparison is by value, rather than by
address; this means that, for example, if two arrays are being
compared, then it is the contents of the arrays, rather than the
pointers to the array memory, that are being compared. No verification
checks are required for these operators.

Numerical values can also be compared using the operators `<` (less
than), `<=` (less than or equal to), `>` (greater than), or `>=`
(greater than or equal to). These can only be used at numeric types,
and implicit casting may be applied to the operands, just as for the
arithmetic operators (see above). The result of these operators is of
type `bool` and will evaluate to either `true` or `false` depending on
the usual meaning of these comparisons. Again, no verification checks
are required for these operators.

As a matter of syntax, it is also possible to "chain" the operators
`==`, `!=`, `<`, `<=`, `>` and `>=`. This means that, for example, `a
< b == c <= d` is a valid expression, which is equivalent to `a < b &&
b == c && c <= d`. Note that all operators in a chain must be in the
same direction, e.g. `a < b > c` is not valid.

The operators `&&` and `||` represent logical "and" and "or"
respectively. These require two boolean operands (no implicit casting
is done) and produce a boolean result with the expected semantics.
Note that evaluation of these operators is "short-circuit";
consequently, while verifying the right-hand operand, the verifier is
allowed to assume that the left-hand operand is true (in the case of
`&&`) or false (in the case of `||`).

Logical implication is also supported via the operators `==>`, `<==`
and `<==>`. `a ==> b` is equivalent to `!a || b`. `a <== b` is
equivalent to `b ==> a`, except that short-circuiting does *not* apply
in this case. Finally, `a <==> b` is true if either `a` and `b` are
both true, or they are both false. Again, there is no short-circuiting
in this case.

Similarly to the relational operators, the implication operators `==>`
and `<==` can be chained, although all chains must point in the same
direction. A chain like `A ==> B ==> C ==> D` is interpreted as `A ==>
(B ==> (C ==> D))`, while a chain like `A <== B <== C <== D` is
interpreted as `((A <== B) <== C) <== D`. Expressions like `A <== B
==> C` will be rejected as this breaks the rule that chains should go
in a consistent direction.



## Function calls

An expression such as `f(e1, e2, e3)`, where `f` is the name of a
function in scope, and `e1`, `e2` and `e3` are other expressions,
represents a function call. (There can be any number of arguments,
zero or more -- 3 is just an example.) At runtime, the argument
expressions will be evaluated, and then the function `f` will be
called. The value of the expression as a whole is equal to the value
returned by the function (at one of its `return` statements). As for
type checking, the types of the argument expressions must match the
function's declared argument types, and then the type of the function
call expression itself is equal to the function's return type (if it
has one).

If the declaration of `f` includes any arguments marked `ref`, then
the actual arguments passed in those positions must be modifiable
expressions (similar to the left-hand-side of an assignment statement
-- see "Assignment statements" below). For example, if `f` is declared
as `function f(ref x: i32)`, then evaluation of the expression `f(a[3])`
would (potentially) cause the array element `a[3]` to be modified as a
side-effect.

Note that for simplicity, the language does not allow side-effecting
expressions to appear in any position other than at the "top level" of
a function call *statement*. This rule is explained in more detail
under "Function call statements" below.

There is also a rule that `ref` arguments are not allowed to "alias"
any other argument. For example, if a function `g` has one ref
argument followed by two non-ref arguments, then the call `g(x, x, 0)`
would be rejected, because the first argument aliases the second. But
a call like `g(x, y, y)` is allowed, because although the last two
arguments alias, neither is a `ref` argument, so the aliasing is
allowed. (The reason for this rule is that verification of functions
with `ref` arguments is somewhat complicated if aliasing between `ref`
arguments is permitted; so to simplify matters, we rule out this
possibility.)

Note that the aliasing checks are part of the verifier, rather than
the typechecker. This is because aliasing may depend on runtime
values. For example, in the call `g(a[i], a[j], 0)`, checking for
aliasing amounts to checking whether `i == j`, which can only be done
knowing the runtime values of `i` and `j`. Thus, in such a case, the
verifier will need to prove that `i != j` (and fail the verification
if this proof cannot be done).

Function arguments (other than `ref` arguments) may be implicitly
converted from one numeric type to another. For example, if a function
`f` expects an `i8`, and `x` is an `i32`, then the call `f(x)` is
valid, with `x` being implicitly converted to `i8`. (In this case, as
with all such type conversions, there needs to be a proof that the
runtime value of `x` is within the range of the new type; if this is
not provable, verification will fail.)

The verifier will also check that all of the function's preconditions
are met at the time when the function is called (if this cannot be
proved, verification will fail). The verifier will then assume, after
the function call is done, that all function postconditions are
satisfied (this assumption will be available for use in any future
proofs).

If the function is generic (see "function declarations" below), then
suitable type arguments will be inferred automatically from the
surrounding context. For example, if `f` is declared as `function
f<T>(x: T)`, and called as `f(123)`, then we already know that `T =
i32` (because the argument has type `i32`) so it is not necessary to
write `f<i32>` explicitly. However, it is always allowed to explicitly
provide the type parameters if desired, i.e. the above call could
equally well have been written `f<i32>(123)` if this was desired for
some reason.

If generic type parameters cannot be inferred automatically, then they
will default to `{}`. For example, if a function `f` is declared as
`function f<T>(): T`, then the expression `f()` (with no other
context) would have type `{}`. But if it had been written within a
statement like `var x: i32 = f();`, or perhaps a statement like
`return f();` (in a context where the return type of the current
function is `i32`), then the compiler is able to figure out in these
cases that the type is `i32` (i.e. that `f` should be interpreted as
`f<i32>` in these cases). (TODO: perhaps the exact type inference
algorithm should be documented in more detail.)

Finally, note that there is a "short cut" syntax for functions that
take exactly one parameter of record or tuple type. Instead of writing
something like `f({1, 2, 3})`, we can write `f{1, 2, 3}` i.e. leaving
out the round brackets. This is only available if the parameter is a
literal tuple or record expression (see below); if the parameter is
merely e.g. a variable of record or tuple type, then the round
brackets are still (of course) needed.


## Tuple and record expressions

A tuple expression looks like `{E1, E2, E3}` where `E1`, `E2` and `E3`
are other expressions. (There can be any number of tuple component
expressions, including zero; three are just shown here as an example.)
This constructs a tuple with the values of the given expressions as
its fields. The type of the tuple expression is `{T1, T2, T3}` where
the T's are the types of the E expressions.

A record expression is similar, except that field names are given,
with each field name being followed by an equals sign and then the
field value expression, as in: `{field1=E1, field2=E2, field3=E3}`.

Note that the order of fields in a record is significant, so e.g.
`{a=1, b=2}` is a different record from `{b=2, a=1}` (and indeed has a
different type).

Examples:

`{1, 2, true}` is a 3-component tuple of type `{i32, i32, bool}`.

`{x=1, y=2, flag=false}` is a 3-component record of type `{x: i32, y:
i32, flag: bool}`.

`{}` is an empty tuple, of type `{}`.

Note:

Fields within tuples and records are never subject to implicit type
conversions. This means that manual casts (see "Casts" below) are
sometimes necessary. For example, if a function `f` requires a
parameter of type `{i8, i8}`, then the call `f{1, 2}` will fail with a
type error (because we are passing a tuple of type `{i32, i32}` and
this cannot implicitly be converted to `{i8, i8}`). Instead, one would
have to do something like `f{i8(1), i8(2)}`.


## Record update expressions

If `R` is an expression of some record type, then `{R with f1=E1,
f2=E2}` is also an expression of the same type, where `f1` and `f2`
are field names and `E1` and `E2` are other expressions. (There can be
any number of fields listed -- one or more -- not just two.)

This expression creates a new record, of the same type as the original
record, but with the fields named `f1` and `f2` (in this example)
replaced with the values of `E1` and `E2` respectively. Any fields not
explicitly mentioned will retain their original values. (Note that the
original record `R` is not changed at all.)

If any of the fields listed (the `f1` and `f2` in this example) do not
exist in the record `R`, then it is a type error.

For example, if `x` equals `{a=1, b=2, c=3}`, of type `{a: i32, b:
i32, c: i32}`, then the expression `{x with b = 1000, c = 2000}` also
has type `{a: i32, b: i32, c: i32}` and is equal to `{a = 1, b = 1000,
c = 2000}`.


## Field projection expressions

If `E` is an expression of tuple type, then `E.0` evaluates to the
first field of the tuple, `E.1` evaluates to the second field, and so
on. E.g. if `x` is equal to `{10,20,30}` then `x.0` equals 10, `x.1`
equals 20, and `x.2` equals 30. (If `x.3` or above were written, this
would be a type error.)

Similarly, if `E` is an expression of record type, and `f` is one of
the field names from that record type, then `E.f` evaluates to the
value of the field `f` of the record. For example, if `x` is equal to
`{foo = 20, bar = 30}`, then `x.foo` is 20 and `x.bar` is 30. (`x.baz`
would be a type error, since no field `baz` exists in the record.)


## Array projection expressions

If `A` is an expression of a one-dimensional array type, and `n` is an
expression of any integer type, then `A[n]` refers to the "nth"
element of the array (elements are numbered starting from zero, and
going up to the size of the array minus one). Similarly, for
multi-dimensional arrays, multiple indices can be given separated by
commas, for example `A[i,j,k]` for a 3-dimensional array.

The verifier will prove that the indices are within the valid range
for the array (i.e. between zero, and the size of the array in that
dimension minus one, inclusive) or else it will issue an error if this
is unprovable. In this way, "array out of bounds" errors cannot happen
at runtime in a verified program.


## Datatype constructors

If `Foo` is the name of a datatype constructor *without* a payload
(see "datatype declarations" below), then the expression `Foo` denotes
an object of the corresponding datatype.

Similarly, if `Foo` is the name of a datatype constructor *with* a
payload, and `E` is an expression of the payload type, then `Foo(E)`
represents an object of the corresponding datatype carrying that
payload. This works like a function call, e.g. if the payload has an
integer type then implicit type casting may occur (just like a
function argument), and if the payload is a record or tuple expression
then the round brackets may be omitted (e.g. we can write `Foo{1,2,3}`
instead of `Foo({1,2,3})`).

Examples:

If we have `datatype Foo = Foo1 | Foo2(i16) | Foo3{i8, i16}`, then:

 - The expression `Foo1` has type `Foo`.

 - The expression `Foo2(100)` has type `Foo`. (The argument `100`,
   being an integer literal, has type `i32`, but this is implicitly
   cast to `i16` when the `Foo2` constructor is "called".)

 - The expression `Foo3{1, 2}` is a type error, because the tuple has
   type `{i32, i32}` and tuples cannot be implicitly cast to a
   different type (see above).

 - The expression `Foo3{i8(1), i16(2)}` is valid and has type `Foo`.

For generic datatypes it is valid to write a datatype constructor
expression either with or without an explicit type argument. If the
type argument is not given, then it will be inferred (similar to
function call expressions). For example, given `datatype Maybe<a> =
Nothing | Just(a);`, then the expression `Just(100)` has type
`Maybe<i32>` because the fact that the type parameter is `i32` can be
inferred in this case. One could equally well write `Just<i32>(100)`
to make the type parameter explicit, if desired. The expression
`Nothing<i32>` would have type `Maybe<i32>`, and the expression
`Nothing` would have type `Maybe<T>` where T is a type inferred from
the context in which the expression appears.


## If-expressions

The formulation `if B then E1 else E2`, where `B` is a boolean
expression, and `E1` and `E2` are expressions of the same type `T`, is
a valid expression and has type `T`. The semantics is that `B` is
evaluated; if `B` is true, then the expression evaluates to `E1`,
otherwise it evaluates to `E2`.

Note that "short-circuit" evaluation is used, so that only one of the
expressions `E1` or `E2` is actually evaluated at runtime. For
example, `if true then 1 else 1/0` is valid, and does not cause a
"division by zero" error, because the `1/0` sub-expression is never
evaluated (because the if-condition is `true`).


## Let-expressions

If `E1` and `E2` are valid expressions, then the expression `let x =
E1 in E2` is valid, and has the same type as `E2`. The semantics of
this is that the expression `E1` is evaluated and temporarily assigned
to the (read-only) variable `x`. The expression `E2` is then evaluated
with this value of `x` in scope, and the result of this evaluation
becomes the value of the entire let-expression. (The variable `x` then
goes "out of scope" again after the evaluation of `E2` is done.)

For example, `let x = 1 + 1 in x + 2` evaluates to 4.


## Quantifier expressions

The keywords `forall` and `exists` can be used to create so-called
quantifier expressions. The syntax is `forall (x: T) E` or `exists (x:
T) E`, where `x` is any valid variable name, `T` is a type, and `E` is
an expression (which must be of boolean type). Within expression `E`,
the variable `x` is in scope and has type `T`. The quantifier
expression as a whole always has boolean type.

The semantics of a `forall` expression is that if expression `E` would
evaluate to `true` under every possible value of `x` (of the given
type `T`), then the `forall` expression as a whole is true, otherwise
it is false. Similarly, the semantics of an `exists` expression is
that if `x` could possibly be assigned some value of type `T` that
would make expression `E` true, then the `exists` expression as a
whole is true, otherwise it is false.

Note that quantifier expressions, by their nature, cannot be evaluated
at runtime, so they are only usable in non-executable contexts. (The
type `T` is therefore allowed to be a non-executable type, such as
`int`, if desired.)

For example:

 - `forall (x: i32) x == x` is true, because no matter what value is
   assigned to `x`, it will always be true that `x == x`.

 - `exists (x: int) x * int(2) == int(4)` is true, because the
   expression `x * int(2) == int(4)` can be made true by setting `x`
   equal to `int(2)`.

 - `exists (x: int) x * int(2) == int(5)` is false, because no
   (integer) value of `x` multiplied by two would give five. However,
   `exists (x: real) x * real(2) == real(5)` would be true.

 - Note that `exists (x: i32) x * 2 == 4` would be an invalid
   expression (it would fail verification). This is because -- as
   noted above under "binary operators" -- when writing any expression
   of the form `a * b` it is necessary to prove that the
   multiplication will not overflow. But in this case, `x` can be any
   `i32` value, and for some `i32` values, `x * 2` would overflow. To
   work around this, we could write something like `exists (x: i32)
   -100 <= x <= 100 && x * 2 == 4`, which asserts that there is an
   integer between -100 and 100 such that two times that integer is
   four. This does successfully verify, because when proving that `x *
   2` does not overflow, the verifier is allowed to assume that `-100
   <= x <= 100` is true (because of the way that the short-circuit
   evaluation of `&&` works) and therefore the proof will succeed.


## Match expressions

Pattern matching can be done using a `match` expression. This has the
general form:

```
match <expr> {
case <pattern> => <expr> ;
case <pattern> => <expr> ;
...
}
```

(The semi-colons are optional.)

The first `<expr>` is called the *scrutinee* and it can be of any type
(as long as it matches the type of the patterns). The scrutinee is
first evaluated, and then matched against each of the patterns in
turn. The first pattern that matches is "accepted"; the entire match
expression then evaluates to the value of the `<expr>` that is to the
right of the accepted pattern.

Each `<pattern>` may be one of the following:

 - A variable name. This pattern always matches. A new variable with
   the given name is created; during evaluation of the `<expr>` to the
   right of the pattern, this new variable will be in scope, and it
   will be equal to the scrutinee.

 - A lone underscore (`_`). This pattern also always matches, but it
   does not introduce any new variable into scope.

 - A boolean or integer literal (e.g. `true` or `123`). These patterns
   require the scrutinee to have boolean or (any) integer type
   respectively (otherwise it is a type error). The pattern will match
   if the scrutinee is equal to the given literal value, otherwise it
   will fail to match.

 - A tuple pattern. This is of the form `{<pattern>, <pattern>, ...}`
   where there can be any number of sub-patterns (0 or more). The
   scrutinee type should be a tuple with the corresponding number of
   fields. Pattern matching continues recursively; each of the
   sub-patterns is matched against a new scrutinee, namely the
   corresponding field of the tuple. (So the first sub-pattern is
   matched against the first field of the tuple, the second
   sub-pattern is matched against the second field of the tuple, and
   so on.) If all of these sub-patterns match, then the tuple pattern
   matches, otherwise it fails to match.

 - A record pattern. This is similar to a tuple pattern but uses the
   syntax `{<fieldname> = <pattern>, <fieldname> = <pattern>, ...}`.
   The scrutinee needs to be of a record type, but it does not need to
   have exactly the same fields as listed in the pattern, nor do they
   have to be in the same order. Instead, the fields listed in the
   pattern merely need to be a subset of the fields actually present
   in the scrutinee. Any fields named in the pattern will be
   recursively pattern-matched (similar to the tuple case), but any
   "other" fields in the scrutinee (i.e. fields that do not appear in
   the pattern) will just be skipped.

 - A datatype pattern. This is of the form `<Name>`, or
   `<Name>(<pattern>)`, where `<Name>` is a data constructor name. For
   type-checking, the scrutinee must be of the correct type (matching
   the datatype that `<Name>` is a constructor for) and if it has a
   payload, the type of the payload must match the given sub-pattern.
   For the pattern to match, the value of the scrutinee must
   correspond to the given data constructor name; and if a payload is
   present, the payload is recursively matched against the given
   `<pattern>` (i.e. the payload is treated as the scrutinee while
   this pattern is matched).

    - Note that if the nested `<pattern>` is a tuple or record
      pattern, then the round brackets may be omitted; e.g.
      `Foo{a,1,_}` is a valid datatype pattern (equivalent to
      `Foo({a,1,_})`).

Some examples may make this clearer:

 - `match 1 { case 0 => 100; case 1 => 101; case _ => 102 }` is equal
   to 101. This is because the first case does not match, but the
   second case does match. (The third case is ignored, because once a
   match is found, no further cases are checked.)

 - If `x` is equal to `{1, 2, true}`, then `match x { case {a, b,
   false} => a; case {a, b, true} => b }` is equal to 2. This is
   because the first case fails to match (because `true` doesn't match
   against `false`); but the second case does match. In the second
   case, the `a` pattern matches against 1, and the `b` pattern
   matches against 2, so this creates new variables `a` and `b` with
   values 1 and 2 respectively. Then, the expression on the
   right-hand-side of the successful match is `b`, therefore the match
   as a whole evaluates to `b`, which has value 2.

 - If we have `datatype Foo = Foo1 | Foo2{i32, i32}`, and `x` is equal
   to `Foo1`, then `match x { case Foo1 => 1; case Foo2(_) => 2 }`
   will evaluate to 1. Similarly, if `x` was `Foo2{100,200}`, then
   that match statement would evaluate to 2 (in this case, the
   "underscore" pattern would match the tuple `{100,200}`). But if the
   match statement was `match x { case Foo1 => 1; case Foo2{x, y} =>
   x+y }` then it would evaluate to 300, because `x` and `y` would be
   matched to 100 and 200, so `x+y` would be 300.

 - If `x = {r=100, g=200, b=255}`, then `match x { case {r=100, b=b}
   => b }` would evaluate to 255. In this case, the pattern states
   that `x.r` must be equal to 100 (which matches), and that `x.b`
   should be assigned to the `b` variable. The pattern doesn't even
   mention the `g` field, but this is valid -- it just means that the
   pattern will match regardless of the contents of that field.
   Similarly, we could also have written `case {b=b, r=100}` and the
   pattern would still match. (Although the order of record fields
   within *expressions* and *types* is significant, the order of
   record fields within *patterns* is not.)

Note that all pattern matches must be *exhaustive*; at least one of
the cases must always match at runtime. This is checked by the
verifier; if a proof that the scrutinee matches at least one "case"
cannot be found, then verification fails. This means that code like
`match x { case 1 => true; case 2 => false }` will (usually) fail
verification (as x could be 3 for example); but if the function had a
precondition that x is either 1 or 2, say, or if this match expression
was within the context of an `if 1 <= x <= 2` or similar, then this
match would be verifiable (because it would easily be provable that x
must be either 1 or 2 in that case).


## Casts

The expression `T(E)`, where `T` is one of the numeric types (`u8`
through `u64`, `i8` through `i64`, or `int` or `real`), and `E` is an
expression of a (possibly different) numeric type, is valid.

At runtime, this expression simply converts `E` to the given type `T`.
If `E` has type `real` and `T` is an integer type, then `E` is
converted to an integer by rounding downwards (towards minus
infinity); otherwise, the numerical value of `E` is left unchanged,
and only its type changes.

If `T` is a finite type (i.e. not `int` or `real`) then the verifier
will check that the value is within the proper range for that type --
if this cannot be proved then verification will fail.

The alternative syntax `cast<T>(E)` is also supported. The advantage
of this (over `T(E)`) is that the `cast<T>` syntax works even if `T`
is a generic type variable, or typedef name, whereas `T(E)` only works
if `T` is one of the keywords `i8`, `u16`, `int`, and so on.

In all cases, the cast must be from one numeric type to another. Casts
of any other type(s) are not supported.

Casts to or from either `int` or `real` are supported only in
non-executable code. All other (valid) casts are supported in both
executable and non-executable code.


## Sizeof expressions

If `E` is an expression of a one-dimensional array type, then
`sizeof(E)` evaluates to the *number of elements* that array E
currently has (as a `u64` value). (Note this is different from
languages like C, where `sizeof` returns a size in bytes.)

If E is of a fixed-sized type, like `i32[10]`, then the result of the
`sizeof` expression will be known at compile time, but if E is an
allocatable or incomplete type (like `i32[*]` or `i32[]`) then
`sizeof(E)` is a useful way to obtain the current size of the array.
Note that `sizeof` is valid in both executable and non-executable
code.

If `E` has a two or more dimensional array type, then `sizeof` will
return a tuple of an appropriate number of `u64` values. For example,
if `E` has type `i32[*,*,*]` then the type of `sizeof(E)` is `{u64,
u64, u64}`.


## Allocated expressions

The expression `allocated(E)` evaluates to `true` if `E` currently
contains allocated heap memory (which must therefore be freed at some
point -- see the section on memory leaks below), or `false` otherwise.

In more detail:

 - If `E` is an allocatable array type (e.g. `i32[*]` or `bool[*,*]`
   etc.) then `allocated(E)` is true if `sizeof(E)` is non-zero (in
   the case of a single-dimensional array), or if *all* components of
   `sizeof(E)` are non-zero (in the case of multi-dimensional arrays).

 - If `E` is a fixed-sized array type, then `allocated(E)` is true if
   `allocated(E[i])` is true for *any* valid array index `i`.

 - If `E` is an incomplete array type, then it is illegal to call
   `allocated(E)` (a type error will result).

 - If `E` is a tuple, record or datatype, then it is allocated if
   *any* of the component fields or payload(s) are allocated.

 - If `E` is an `extern` type (see below) that was marked
   `(allocated)` in its declaration, then `allocated(E)` is true if
   `E` is not equal to the default value for that type. If the
   `extern` type was marked `(allocated_always)`, then `allocated(E)`
   is always true. If the `extern` type was not marked in either of
   those ways, then `allocated(E)` is false.

 - In all other cases, `allocated(E)` is false.

Note that `allocated` can only be used in non-executable code.



# Statements

Statements may appear inside function declarations (see Declarations below).

## Variable declarations

Variable declaration statements have one of the following forms:
 - `var <name>: <type>;`
 - `var <name> = <expression>;`
 - `var <name>: <type> = <expression>;`

For example, `var x = 1;` or `var i: i32;` are valid variable declarations.

The effect of a variable declaration statement is to create a new
variable, with the given name, and having the given type (or if no
`<type>` is given, then having the same type as the given
`<expression>`). If an `<expression>` is given then the variable is
initially equal to the value of that expression; otherwise, the
variable initially has the default value of the given type, which is
as follows:

 - `bool` variables default to `false`.

 - Numeric variables (types `i8` through `i64`, `u8` through `u64`, or
   `int` or `real`) default to zero.

 - Records or tuple variables default to a record or tuple in which
   all fields have the default value for their respective types.

 - Datatype variables default to the first constructor listed in the
   datatype declaration. If this constructor has a "payload", then the
   payload will have the default value for its own type.

 - For fixed-sized arrays, the elements will all have the default
   value for the element type of the array.

 - For allocatable arrays (`T[*]`), the array will by default have
   size zero.

Note that `int` or `real` types (or records, tuples or datatypes
containing these) can only be created in ghost code (see "Ghost
prefix" below). Variables of "incomplete array types" (`T[]`) cannot
be created at all in a variable declaration statement.

The new variable will be in scope until the end of the current "block"
(a block is either a function body, the "then" or "else" part of an
`if` statement, the main body of a `while` statement, the
"right-hand-side" of each `case` of a `match` statement, or the
"proof" part of an `assert` statement). It is allowed for a variable
in one block to shadow a variable of the same name in an outer block,
but it is not allowed for a variable to have the same name as a
previous variable in the same block.


## Reference declarations

A reference declaration takes the same form as a variable declaration,
but it uses the word `ref` in place of `var`, for example, `ref r =
a;` or `ref r = a.b.c;`.

In this case, the form `ref <name>: <type>;` cannot be used, but
either `ref <name> = <expression>;` or `ref <name>: <type> =
<expression>;` are valid.

The `<expression>` in a ref statement must be an "lvalue"; that is to
say, either a variable name, or a field projection or array projection
expression in which the left-hand side is itself an lvalue.

A ref statement creates a "reference" to the right-hand-side
expression; effectively, the right-hand-side expression is substituted
anywhere that the ref variable appears. For example, in:

```
var x: i32[10];
ref r = x[4];
r = r + 1;
```

the last statement is actually equivalent to `x[4] = x[4] + 1;`.

There is also a rule (currently) that it is illegal to create a
reference to an element of an allocatable array. This is to prevent a
situation where e.g. a reference is created to `a[9]` for some array
`a`, but then `a` is resized to have fewer than 10 elements (so that
`a[9]` is no longer a valid element of the array).


## Assignment statements

The statement `<expression> = <expression>;` is an assignment
statement. (For example, `x = 1;` or `x[10].fieldname = y + z;`.)

The left-hand side of an assignment must be an lvalue expression (see
definition of "lvalue" above) which is not read-only.

The right-hand-side can be any valid expression of the same type as
the left-hand-side (or a "compatible" type in the sense that implicit
casts between numeric types may occur).

The effect of the statement is simply to change whatever the
left-hand-side refers to (variable, array element, etc.) such that it
is equal to the value of the right-hand-side.

An important restriction on assignment statements is that the
right-hand-side of the assignment must not be "allocated" (i.e. if the
right-hand-side expression is `E`, then `allocated(E)` must be false).
This is because copying such an expression would require new memory to
be allocated, which might not be possible (if the system is low on
memory) and therefore there would be no guarantee that the assignment
could be completed successfully.


## Function call statements

A function call statement takes the form: `<lhs expression> =
<function call>;` or `<function call>;`, where `<function call>` is a
valid function call expression (see "Function calls" under
"Expressions" above).

If the function being called returns a value, then the first form must
be used and the `<lhs expression>` must be a writable lvalue
expression (similar to the left-hand-side of an assignment statement)
of the same type as the function's return value (or a "compatible"
type in the sense that implicit casts between numeric types may
occur). If the function being called does not return a value, then the
second form must instead be used.

As was mentioned above (in the description of function call
expressions), the only place in the language where a function with
"ref" arguments can be called is at the "top level" of a function call
statement. For example, if `f` is declared as:

```
function f(ref x: i32): i32
{
    x = 1;
    return 2;
}
```

then the call `v = f(b[3]);` would be valid (assuming the array `b`
has at least four elements); this would set `b[3]` to 1 (since this is
what the function `f` does to its ref argument) and it would also set
`v` to 2 (because this is what `f` returns). But statements like
`foo(f(b[3]));` (which is trying to pass the return value from `f` to
another function `foo`), or `v = f(b[3]) + 1;` (which is trying to add
1 to the return value before assigning it to `v`), would be rejected,
because in these cases the function with the ref parameter is not
appearing at the "top level" of the function call statement, but
nested within some other expression.


## Swapping two values

If `e1` and `e2` are two writable lvalue expressions (i.e. expressions
which could validly appear on the left-hand-side of an assignment
statement), then the expression `swap e1, e2;` is valid. This simply
"swaps" the values of `e1` and `e2`, i.e. it is similar to the
sequence:

```
var tmp = e1;
e1 = e2;
e2 = tmp;
```

except that the `tmp` variable is not actually constructed; instead
the values are just swapped "in place". This means in particular that
`swap e1, e2;` is permitted even if `allocated(e1)` or `allocated(e2)`
are true (whereas the above sequence involving a `tmp` variable would
not be permitted in that case).


## Return statements

The statement `return e;` (where `e` is an expression of the same type
as the current function's declared return type, or a type implicitly
convertible to it via a numeric "cast") immediately returns from the
current function, setting the return value of the function to the
value of `e`. It is not permitted to return an allocated value (i.e.,
`allocated(e)` must be false; the verifier will check this).

Similarly, `return;` immediately returns from the current function,
returning no value (this is used for functions that do not declare a
return type).

The verifier checks that any postconditions of the current function
are true at the return statement, and that no allocated variables are
still in scope at this point (see also "Memory leak prevention"
below).


## If statements

The statement `if <condition> { <statements> } else { <statements> }`
evaluates the condition (a boolean expression) and then executes the
first block of statements if the condition is true, or the second
block if it is false. Execution then continues from the next statement
after the if-statement.

The `else` part can be omitted, in which case the if-statement just
does nothing when the condition is false. (In other words, if the
`else { <statements> }` part is omitted, then it is as if `else { }`
had been written in its place.)

During verification of the "then" part of the if-statement, the
verifier will assume that the condition is true. During verification
of the "else" part (if any), the verifier will assume that the
condition is false. (These assumptions are usable in any proofs that
might be required.)


## While statements

A while statement has the form

```
while <condition>
    invariant <expression>;
    invariant <expression>;
    decreases <expression>;
{
    <statements>
}
```

There can be zero or more `invariant`s. The `decreases` clause must be
present if the program is to be verified (although it can be left out
if one desires only to run the program without verifying it). There
can be at most one `decreases` clause.

The `<condition>` should be a boolean expression. At run time, if the
condition is true, the program will enter the body of the while loop
(the `<statements>`). At the end of those statements, execution
returns back to the `while` statement (hence if the condition is still
true, then the loop is entered again). Alternatively, if the condition
is false, the code will skip the body of the loop and resume execution
from the next statement after the final `}` of the while-statement.

The invariant expressions (which must be of boolean type) are not
executed at runtime, and may therefore contain non-executable
constructs (such as ghost variables or quantifier expressions).
Instead, the verifier will prove that the invariant expressions are
all true, at both the beginning and end of the loop.

The decreases clause is also not executed at runtime. The `decreases`
expression is required to be one of one of the types `bool`, `int`,
`i8` through `i64`, `u8` through `u64`, or tuples of these (possibly
nested).

The verifier will prove that the value of the `decreases` expression
has strictly decreased, according to the following ordering, between
the start and end of the loop:

 - For `bool`, `false` is considered lower than `true`.

 - For integers, the usual ordering on integers is used.

 - For tuples, lexicographic ordering is used (e.g. `{A, B}` is less
   than `{C, D}` if either `A < C` or `A == C && B <= D`).

Note also that if `int` values are used anywhere in a decreases
expression, then the verifier will also prove that these values are
greater than or equal to zero. (This restriction does not apply to the
finite-integer types like `i8` or `u16` as these already have a
natural lower bound.) This ensures that all `decreases` values are
bounded below.

The above considerations mean that if a program passes verification,
then any while-loops in the program must terminate after a finite
number of iterations.

We also need to explain what assumptions the verifier makes when
verifying the loop body (and also any statements after the loop). The
rule is that if a variable is not explicitly modified during the loop
body (e.g. by assignment statements, passing to function `ref`
parameters, etc.) then the verifier can assume that it still has the
value it had before the loop was entered. But if a variable *is*
modified during the loop, then the verifier can make no assumption
about it; it could potentially have any value (of the correct type) at
the start of the loop body. The verifier then makes the following
additional assumptions:

 - At the start of the loop body, the loop condition is *true*, and
   the invariants are all *true*.

 - After the loop is exited, the loop condition is *false*, and the
   invariants are all *true*.

An example may help illustrate this:

```
var i: i32 = 10;
var j: i32 = 20;

while j > 0
    invariant j >= 0;
    decreases j;
{
    // At this point, because j is modified by the loop code (but i
    // isn't), the verifier assumes that i == 10, but j could have
    // any i32 value.

    // To this, the following assumptions are added:
    //  j > 0   (because the loop was entered)
    //  j >= 0  (because this is the invariant)
    // This is equivalent to just assuming j > 0, of course.

    // Therefore, the following statement can successfully be
    // verified, because j > 0 and hence j - 1 is within the
    // range of an i32.
    j = j - 1;

    // At this point, the verifier must now prove that the invariant
    // (j >= 0) is still true. This proof is straightforward, because
    // the original assumption was that j > 0, so it follows that
    // even after executing "j = j - 1", we still have that j >= 0.

    // The verifier must also now prove that the "decreases"
    // expression (i.e. "j") has decreased, but again this is easy,
    // because the verifier can see that the new value of j is one
    // less than the old.
}

// When we get here, the verifier assumes that i == 10
// (because i was not modified by any loop statement), but that j
// could have any i32 value (because j is modified during the loop).
// To this, the following assumptions are added:
//  !(j > 0)    (because the loop was not entered)
//  j >= 0      (because this is the invariant)

// Hence, the following assert is provable, because it follows
// directly from these assumptions:
assert j == 0;
```


## Match statements

In addition to match expressions (see above), there are also match
statements. These work exactly the same as a match expression, except
that where previously there was an expression on the right-hand-side
of each case, now there is a list of statements:

```
match <expr> {
case <pattern> => <statements>
case <pattern> => <statements>
case <pattern> => <statements>
}
```

There can be any number of cases (one or more).

When execution reaches a `match` statement, the corresponding `case`
is found and then the block of statements corresponding to that case
(and only that case) is executed. (This block of statements could be
empty; if so, the match statement is just skipped entirely, in that
case.)

As with match expressions, match statements are required to be
exhaustive -- the verifier will prove that at least one of the cases
matches successfully.

An example of a match statement:

```
match x {
case 1 => println("x is one!");
case 2 => println("x equals 2");
case _ => // Do nothing
}
```

There is one additional feature that match statements have, which
match expressions do not have, and that is that variable patterns can
be matched either by *reference* or by *value*. This is done by either
preceding the variable name with the keyword `ref`, or by not doing
so, as in:

```
var x: {i32, i32} = ...;
match x {
case {1, ref a} =>  // 'a' matched by reference
case {2, b} =>      // 'b' matched by value
}
```

The meaning, in short, is that if a variable `a` is matched by
reference, then it is just a reference or pointer to part of the
original scrutinee; no copy is made. If it is matched by value, then
the variable is a full copy of that part of the original scrutinee.

A restriction is that if any variable pattern in any of the cases is
being matched by reference (i.e. is marked `ref`), then the scrutinee
must be an lvalue (i.e. either a variable, or a field or array
projection applied to another lvalue). However, it does not have to be
a *writable* lvalue; e.g. it could be a (read-only) function parameter
variable.

A further restriction is that if a non-`ref` variable pattern is used,
then the part of the scrutinee that is matched into that variable must
*not* be `allocated`. (This is to prevent any potential copying of
allocated values at runtime, which might result in memory leaks or
double-free bugs etc.)

Also note that in match statements, any variables created in patterns
are *writable*. The only exception is that if the scrutinee was
non-writable and the variable pattern was marked `ref` then it becomes
a non-writable variable instead.

Some examples may help to clarify this. Imagine we have:

```
var x: {bool, i32} = ...;
match x {
case {true, ref a} => a = 123;
case {false, b} => b = 456;
}
```

If `x.0` was `true`, then the first case would execute, and a variable
`a` would be created as a reference (or "pointer") to `x.1`. Hence any
writes to `a` would modify `x.1`, and therefore, after this code
executes, `x.1` would be equal to 123.

If, instead, `x.0` was `false`, then the second case would execute. A
new `i32` variable called `b` would be created, and this would be set
equal to `x.1` initially. The code then sets `b` to 456, but then the
variable `b` is discarded without being used for anything else, which
means that the value of `x.1` is unchanged by this code (in
particular, it is *not* set to 456 in this case).

Now consider the following:

```
function f(x: {bool, i32})
{
    match x {
    case {true, ref a} => a = 123;  // Illegal
    case {false, b} => b = 456;     // Legal
    }
}
```

In this code, the match of `x.1` against `ref a` is legal, but `a` is
a *read-only* reference in this case, so the write `a = 123;` is
illegal. By contrast, the match of x.1 against `b` creates a new
variable, so the write `b = 456;` is allowed.


## Assert statements

The simplest form of `assert` statement is `assert <expression>;`
where `<expression>` is a boolean expression.

The assert statement is not executed at runtime. Instead, it is an
instruction to the verifier to prove that `<expression>` is true at
this point in the program. If the verifier cannot prove this, then
verification will fail.

Since the `<expression>` is not executed, it is allowed to include
"ghost" constructs, such as `forall` expressions or references to
ghost variables.

A more complicated form of `assert` allows a "proof" of the assertion
to be included. This has the form `assert <expression> { <proof> }`
where the `<proof>` is simply a sequence of statements. All of the
statements in the proof are considered non-executable (so can include
"ghost" constructs). The proof is usually a sequence of `assert`
statements, showing the "reasoning steps" that are required to prove
the original assertion. Proofs also often include `if` statements (to
do a proof by cases) or `while` statements (to do a proof by
induction). Proofs can also include `fix` and `use` statements to help
prove `forall` and `exists` expressions (see below for details).

The form `assert *;` can also be used, within a proof, as a shorthand
for asserting the original expression that was to be proved (in the
original `assert` statement that opened the proof).

For example, we might have something like this:

```
assert i > 10
{
    if x < 5 {
        assert *;
    } else {
        assert *;
    }
}
```

Here, each `assert *;` is short for `assert i > 10;` (because `i > 10`
is the thing that we are trying to prove). This code is basically
instructing the verifier to split the proof of `i > 10` into two
cases, depending on whether `x < 5` or not. 


## Fix statements

The fix statement is used within the proof block of an assert
statement, and specifically when the expression being asserted is a
`forall` expression.

The syntax is `fix <name>: <type>;`.

The effect of this is to replace the "goal" of the assert, `forall (x:
<type>) <expr>`, with just `<expr>` (with `<name>` being substituted
in place of `x`, if it is different).

For example, if one wanted to prove `forall (x: i32) P(x)` (for some
property P) and one wanted to split the proof into cases depending on
whether x was >= 0 or < 0, then one might write:

```
assert forall (x: i32) P(x)
{
    fix i: i32;
    // The goal is now "assert P(i)" instead of "forall (x: i32) P(x)"
    if i >= 0 {
        assert *;   // Equivalent to "assert P(i)" (under the assumption i >= 0).
    } else {
        assert *;   // Equivalent to "assert P(i)" (under the assumption i < 0).
    }
}
```

Note that `fix` may only appear at the "outermost" level of a proof.
For example, the following is invalid:

```
assert forall (x: i32) P(x)
{
    if y > 10 {
        fix x: i32;  // Illegal: fix must appear at top level, not
                     // nested within an if, while, etc.
        // ...
    } else {
        // ...
    }
}
```


## Obtain statements

The "obtain" statement creates a ghost variable that satisfies a
certain boolean condition. The syntax is `obtain (<name>: <type>)
<expression>;`, where `<expression>` must be a boolean expression.

For example, `obtain (x: i32) x > 0;` creates `x` as a ghost `i32`
variable. The value of `x` is not known, but we do know that `x > 0`.

The verifier will check that a condition of the form `exists (<name>:
<type>) <expression>` can be proved (if not, the "obtain" statement will
fail verification).

"Obtain" statements are non-executable statements (they are just
skipped at runtime), so the `<expression>` can include ghost
constructs (such as quantifier expressions or references to ghost
variables). Also, the variable created by "obtain" is a ghost variable
so it cannot be used in any executable expression or statement later
on.

"Obtain" statements are useful when you know that a value meeting some
condition exists, but you need an actual value that meets the
condition, for use in a proof or something similar.


## Use statements

A "use" statement is used within the proof block of an `assert`, and
specifically when the expression being asserted is an `exists`
expression.

If the expression being asserted is `exists (x: <type>) P(x)`, and a
`use E;` statement is encountered, the verifier convert the goal of
the assert into `P(E)` instead. (It is necessary that `E` has the type
`<type>`, otherwise type-checking will fail.) Note that if `P(E)` can
be proved, then it is certainly the case that `exists (x: <type>)
P(x)` is true, so this transformation is a valid thing to do.

A trivial example is the following:

```
assert exists (x: i32) x > 10
{
    use 11;
}
```

Here, the `use` statement converts the goal from `exists (x: i32) x >
10` to `11 > 10`, which is easily provable. (To be fair, in this case,
most verifiers would be able to prove `exists (x: i32) x > 10` without
any help. But in more complicated cases, if we are trying to prove
there exists some `x` such that `P(x)`, then the verifier might not be
able to "find" such an `x` on its own; but if we "tell" it which `x`
to use, in a `use` statement, then the verifier now just has to prove
that the given value does indeed satisfy `P(x)`, which is a much
easier thing to do.)


## Show and hide statements

Usually, the verifier is allowed to "look inside" the definitions of
functions during its proofs. For example, given:

```
function f(x: i32): i32
    requires x < I32_MAX - 1;
{
    return x + 1;
}
```

then the statement `assert f(0) == 1;` would verify successfully,
because the verifier is allowed to "look inside" the definition of `f`
to see that f(0) = 0 + 1 = 1. (Technically speaking, the verifier will
pass the definition of `f`, which is effectively "Let f(x) = x + 1",
to the SMT solver, which can then use this to prove that "f(0) = 1" is
a mathematically true statement.)

However, sometimes assertions can be proved without needing to
actually expand out the full definition of a function. (For example,
we might be able to prove things using only the postconditions of a
function, without needing to see the full definition.) In these cases,
it can actually be counterproductive to send the full definition to
the SMT solver, as the solver might then get bogged down in repeatedly
trying to expand out the definition, unnecessarily, thus failing to
see a simpler proof that only uses the function's postconditions (or
whatever else is available).

Therefore, the "hide" facility is provided. The statement `hide f;`
means that the verifier will not consider the full definition of the
function `f` in any of its future verifications (although the pre and
post conditions of `f`, if any, will still be taken into account). The
`hide` statement lasts until the end of the code block in which it
occurs, or until a subsequent `show f;` statement (whichever happens
first).

Note that in a `hide f;` or `show f;` statement, `f` must be the name
of a function; it is not possible to hide local variables or
constants, for example.


## Assume statements

The statement `assume <expression>;` tells the verifier to just assume
that the boolean expression `<expression>` is true, without proof.
This assumption lasts until the end of the code block in which the
`assume` statement is found.

This can be used in cases where the programmer "knows" something is
true, but the verifier being used is unable to prove it. It can also
be used in order to defer proofs until a later time (`assume false;`
is sometimes used for this purpose, since assuming `false` allows any
condition to be proved).

Note that an incorrect `assume` statement can compromise the soundness
of the verification, so `assume` statements should only be used with
extreme caution.


## Ghost Statements

Any of the statements listed above can be preceded by the keyword
`ghost`. This turns the statement from an executable into a
non-executable statement. In other words, statements marked in this
way will not execute at runtime (they are treated as "nops") but they
will still affect the verifier.

The precise effect of the `ghost` keyword on each of the statement
types is as follows:

 - A ghost variable declaration statement (such as `ghost x: i32 =
   1;`) will create a ghost variable. Ghost variables do not exist at
   runtime, but they still exist at verification time, so for example
   they can be updated (by ghost assignment statements), or used in
   assertions, or used in while loop invariants.

    - Note that it is an error if any executable statement depends on
      the contents of, or attempts to change, a ghost variable. For
      example if a (non-ghost) `if` statement tests the value of a
      ghost variable, or if a (non-ghost) assignment statement tries
      to write to a ghost variable, these would be compile-time
      errors.

    - Going the other way, ghost statements (such as ghost "if"
      statements or ghost assignments) are allowed to inspect the
      contents of non-ghost variables, but a ghost statement cannot
      modify the value of a non-ghost variable in any way.

 - A ghost assignment statement is used to assign to a ghost variable.
   For example, `ghost x = 2;` sets the ghost variable `x` to 2. (This
   statement would be an error if `x` was not a ghost variable.)
   Similarly, `ghost swap` statements can be used to swap ghost
   variables.

 - A ghost function call statement is useful e.g. for calling ghost
   functions, or when passing ghost variables as `ref` parameters. A
   ghost call statement won't actually call the function (at runtime),
   but it will still check preconditions, and any postconditions of
   the call will be known to be true after the call completes. Also
   any ghost variables passed as `ref` parameters will be updated as a
   result of the call.

 - `ghost return` is not allowed, except when the current function is
   declared `ghost` (but in that case, one might as well use a plain
   `return` instead, since all statements inside a `ghost` function
   are implicitly assumed to be marked `ghost`).

 - If `ghost if`, `ghost while` and `ghost match` are used, then all
   statements within the body of the `if` or `while`, or within the
   cases of the `match`, will automatically become ghost statements as
   well (whether explicitly marked as such or not). In addition, the
   if or while condition, or match scrutinee, now become
   non-executable expressions (so they are allowed to include ghost
   variables, `forall` quantifiers, etc).

 - There is no effect if `ghost` is used with `assert`, `fix`,
   `obtain`, `use`, `show`, `hide` or `assume`, because these
   statements are always implicitly considered to be ghost statements
   anyway (there is no need to explicitly mark them `ghost`).


# Declarations

The top level of a Babylon module consists of a set of declarations.
As explained in the "Modules" section below, these are divided into
interface and implementation declarations.

Declarations can depend on other declarations (for example, if a
constant `y` is defined to be `x + 1`, where `x` is another constant,
then `y` depends on `x`). There is no requirement to list declarations
in dependency order; the compiler will automatically process
declarations in an appropriate order, such that "dependent"
declarations will always be processed after the things that they
depend on.

However, recursion is not currently permitted; no declaration can
depend on itself, nor can a group of declarations depend on each other
in a "circular" manner. (This rule will hopefully be relaxed, at least
to some extent, in a future version of the language.)

The four types of declarations available are `type`, `datatype`,
`const` and `function`. We now describe each of these in turn.


## Type declarations

The `type` declaration has several purposes.

### Typedefs

A declaration of the form `type <name> = <type>;` is known as a
"typedef". This just defines `<name>` (an identifier) to be a synonym
for the given type. Thus, for example, `type MyInt = i32;` defines
`MyInt` as a synonym for `i32`. An `i32` value can be used wherever a
`MyInt` is expected, and vice versa.

Typedefs can also be "generic", i.e. have type parameters. For
example, `type Pair<a,b> = {a,b};` declares that `Pair<a,b>` will be a
synonym for the type `{a,b}`, for any types `a` and `b` (e.g.,
`Pair<i32, bool>` could then be used as a synonym for `{i32, bool}`).

If a typedef (with a particular name) is given in a module's
interface, then no `type` or `datatype` declaration of the same name
may appear in the module's implementation. The reverse is also true,
except that a typedef in the implementation may be redeclared in the
interface as an "abstract type" (see below).


### Abstract types

A declaration of the form `type <name>;` (where `<name>` is an
identifier) creates an abstract type. An abstract type declaration
must appear in the module's interface, and there must be a
corresponding declaration (either a non-abstract `type` declaration,
or a `datatype` declaration, for the same `<name>`) in the module
implementation.

An abstract type "hides" the details of the type from other modules.
For example, if module `M` declares `type Foo;` in the interface, and
`type Foo = {i32,i32};` in the implementation, then it would be legal
for other modules (that import `M`) to create and copy around values
of type `Foo` (this includes declaring a default-initialized variable
of type `Foo`, passing a `Foo` to a function, assigning a `Foo` to
another variable, receiving a `Foo` return value from a function, and
so on); but those modules would not know anything about the contents
of a `Foo` value (other than that it is not `allocated`). In
particular, those other modules would not be able to "look inside" a
`Foo` value to project out the tuple components, nor do anything else
that relies on knowing what the concrete type underlying the name
`Foo` actually is.

It is also possible to declare an abstract type using the syntax `type
Foo (allocated);` or `type Foo (allocated_always);`. This means that,
if `x` has type `Foo`, then (in the former case) `allocated(x)` is
true if and only if `x` is equal to the default value of a `Foo`
object, and (in the latter case) `allocated(x)` is always true.

It is a rule of the language that the "allocated level" of an abstract
type must be compatible with the implementation given for it. If the
abstract type (in the interface) is declared with neither
`(allocated)` nor `(allocated_always)`, then the concrete type (in the
implementation) must not include any allocatable array type anywhere
within it, nor must it include any type that is itself `(allocated)`
or `(allocated_always)`. If the abstract type is declared
`(allocated)` then the concrete type must not include anything marked
`(allocated_always)`. If the abstract type is `(allocated_always)`
then the concrete type can be any type whatsoever.

Note that abstract types may not be "generic" (in the current version
of the language). For example, `type Pair<a,b>;` (in the module
interface) is illegal, even though `type Pair<a,b> = {a,b};` (in the
module implementation) is valid.


### Extern types

A final form of the `type` declaration is the so-called "extern type".
This is useful when interfacing with the external environment
(currently this means C functions, but perhaps the definition of
"external environment" will be expanded to include other languages or
interfaces in the future).

The declaration `extern type Foo;` creates a type named `Foo` which
corresponds to a `void *` pointer in C.

On the Babylon side, `Foo` functions similarly to an abstract type;
the Babylon code can create default values of this type (corresponding
to C `NULL`), pass them to functions, and so on, but it cannot "look
inside" the type to see what the `void *` pointer contains or what it
points to.

It is also possible to declare an extern type as `extern type Foo
(allocated);` or `extern type Foo (allocated_always);`. This means
that, on the Babylon side, values of type Foo will be considered
"allocated" if the C void pointer is non-NULL (in the former case) or
just always considered "allocated" (in the latter case). In
particular, `(allocated)` is useful if the C void pointer points to
some sort of allocated memory (as this will prevent the pointer being
"leaked" or duplicated on the Babylon side).

If a type is declared using `extern type` in the module interface then
no `type` or `datatype` declaration bearing the same name may appear
in the module implementation. The reverse is also true, with the
exception that the type declared using `extern type` in the module
implementation may be redeclared as an abstract type (see above) in
the module interface.

Note that extern types do not necessarily have to be used with C (or
any other external language) at all; sometimes it is useful to have a
purely "uninterpreted" type, where we know that values of that type
exist, but we do not know anything else about them. An `extern type`
declaration will create such a type.

However, the main application for "extern types" is, as mentioned, to
use them to interface with other languages (such as C). In this case
they will most likely be used with "extern functions"; see below for
more information about those.

Note that "extern" types cannot have type parameters (in the current
version of the language). For example, while `extern type Foo;` is
allowed, `extern type Foo<a>;` is not.


## Datatype declarations

The `datatype` declaration creates a new type which represents a
"union" of different possible values. It is similar to a Haskell or ML
"datatype" or a Rust "enum" type.

The syntax is best described by example. The most basic form of
datatype is defined as a list of one or more names (called
"constructors"), as in:

```
datatype Color = Red | Green | Blue;
```

Here `Color` is the datatype name, and `Red`, `Green` and `Blue` are
the constructors.

This simply means that a value of type `Color` is one of the three
possible values `Red`, `Green` or `Blue`.

It is also possible for each constructor to (optionally) have an
attached "payload type", as in for example:

```
datatype Item = Number(i32) | Pair(i32, i32) | None;
```

This means that a value of type `Item` can have the values `Number(x)`
where `x` is any `i32` value; `Pair(x, y)` where `x` and `y` are
arbitrary `i32` values; or `None`.

To construct a datatype, one simply writes the constructor name
followed by the desired payload value (if any) in round brackets; for
example, `Number(123)` is a valid term of type `Item`, and so is
`Pair({1, 2})`. (In the latter case, the round brackets can also be
omitted if desired, as in `Pair{1, 2}`.) See also "Datatype
constructors" under "Expressions" above.

Datatypes may also have generic type parameters. For example,
`datatype Maybe<a> = Nothing | Just(a);` defines a datatype with two
constructors; the values of this type are `Nothing` and `Just(x)`
where `x` is any value of type `a`. Because the Maybe type has been
declared generic, it can be used with different type parameters, e.g.
`Maybe<i32>`, `Maybe<bool>` and `Maybe<{i32,u64}>` are all valid
types.

It is not (currently) possible to use the built-in `==` operator with
datatypes, except in ghost code. Instead, to check (within executable
code) whether a value equals a particular constructor, a `match`
expression or statement must be used. The `match` can also be used to
extract the payload value if there is one. See also "Match
expressions" and "Match statements" above.

If a `datatype` declaration is given in the module interface then no
`type` or `datatype` of the same name is allowed in the module
implementation. The same is true in reverse, except that the datatype
can be declared abstract in the interface if desired (see "Abstract
types" above).


## Constant declarations

A constant declaration simply takes the form `const <name> = <value>;`
or `const <name>: <type> = <value>;`. In both cases `<value>` must be
an expression whose value is known at compile time. If the `<type>` is
given then this must match the type of the `<value>` (with the usual
proviso that implicit conversions from one finite-sized integer type
to another, e.g. `i8` to `i16` or similar, are allowed).

The effect of a const declaration is simply to arrange that the name
`<name>` (if not shadowed by some local variable) acts as a "global
variable" whose value is equal to the given `<value>` at all times.
This "global variable" is considered read-only and cannot be modified
by any statement or other language construct.

In the module interface it is also possible to have `const <name>:
<type>;` which means that (as far as other modules importing this
module are concerned) the given name is known to be a constant of the
given type, but its precise value is unknown. In this case there must
also be a corresponding declaration of the form `const <name> =
<value>;` or `const <name>: <type> = <value>;` (with the same name) in
the module's implementation, giving the value of the constant. Apart
from this one exception, it is never permissible for two `const` or
`function` declarations at different places within the same module to
share the same name.

Note that "ghost constants" are not allowed currently. Also, generic
constants (e.g. something like `const foo<a> = ...`) are not allowed.


## Function declarations

There are two kinds of functions: "normal" functions with an
implementation in the Babylon language, and "extern" functions which
are assumed to be implemented in some other programming language (e.g.
C) and linked in separately.

### Normal functions

A normal function has this general form:

```
function <name>(<name>: <type>, ...): <return-type>
    requires <condition>;
    ...
    ensures <condition>;
    ...
{
    <statements>
}
```

First the word `function` is given followed by the name of the
function (which must be a valid identifier). Then, within a pair of
round brackets, the names and types of any arguments are given.
Finally, we write a colon followed by the return-type of the function
(we can also omit the colon and the return-type, for functions that do
not return a value).

After that, we can write zero or more `requires` conditions -- these
are boolean expressions that are required to be true at call sites.
The verifier will prove that all function preconditions are satisfied
at runtime at each call site. Following that are zero or more
`ensures` conditions -- these are boolean conditions that are true at
the end of the function. The verifier, when checking the function
body, will prove, at every `return` statement and at the end of the
function (if applicable), that all of the postconditions are true. At
call sites, the verifier will also be able to assume (without further
checks) that all function postconditions are true.

After the requires and ensures conditions (if any) the function body
is written. This is simply a list of statements enclosed in `{` and
`}`. Within the function body, the function arguments are considered
to be read-only variables of their declared types.

(Note that, in terms of the compiled code, the function arguments are
usually passed either in registers, if they are small enough, or as
pointers, for larger values. This means that, for example, large
tuples and records can be passed as arguments without inefficiency.)

It is also possible to write a function declaration without including
a function body, but this can only be done in the module interface,
and in this case, a corresponding declaration, which *does* include
the function body, must be written in the module implementation. The
types (but not necessarily names) of all arguments must be the same,
and the return type must be the same, between the two declarations.
The requires and ensures conditions do not necessarily have to be
identical, but the requires-conditions of the interface declaration
must logically imply the requires-conditions of the implementation
declaration, and the ensures-conditions of the implementation
declaration must imply the ensures-conditions of the interface
declaration.

Apart from the case described above, no two `function` declarations in
a module can have the same name, nor can a `function` have the same
name as a `const` in the same module.

Not shown in the above syntax description, the word `ref` can also be
added to any of the function arguments, to convert the argument into a
"ref argument". Ref arguments are discussed under "function calls"
above, but basically, this means that the argument variable is
considered read-write (not read-only) within the function; and that
any changes made in the function are propagated back to the caller.
(In this case, the caller is required to pass some sort of modifiable
value, such as `x` or `a[1]`, for the actual argument; expressions
like `1` or `x + 3` would not be allowed.)

Note that the word `ref` can either come just before the argument
name, or just after the colon (before the type); there is no
difference between these forms -- they are just alternative syntaxes.

Here is an example of using `ref` arguments:

```
function swap_two_numbers(ref x: i32, ref y: i32)
{
    swap x, y;
}
```

Note that, if any `ref` arguments are present, and if those `ref`
argument variables are mentioned in any of the function's "ensures"
conditions, then a question arises: should the `ensures` condition be
evaluated using the "old" values of those variables (before the
function was called) or the "new" values (after the function has
completed)? The answer is that by default, the "new" value is used,
but if the variable name appears within an `old` marker, then the
"old" value is used instead. For example:

```
function test(ref x: i32)
    requires 0 <= x <= 100;
    ensures x == old(x) + 1;
```

This means that after a call such as `test(y);`, the variable `y` (in
the caller's scope) will be equal to the value it had before the call,
plus one.

The `old` marker does not have to just enclose a variable name; it can
enclose an entire expression, in which case the `old` modifier will
apply to all variables that occur within that expression. For example,
the above postcondition could have been written `ensures x == old(x +
1);` instead, and it would have the same meaning. (This could be read
as: "after the call, `x` will have the same value that `x + 1` had
before the call".)

Note that `old` can only be used within postconditions, not anywhere
else in the language.

Also note that the keyword `return` can be used as an expression
(again, only within postconditions), to refer to the return value of
the function. For example, the following function guarantees that its
return value will be between 0 and 10 inclusive:

```
function foo(x: i32): i32
    requires 0 <= x <= 100;
    ensures 0 <= return <= 10;
```

Another feature (not shown above) is that function declarations can be
marked "ghost", by writing `ghost` immediately before the word
`function`, if desired. A ghost function cannot be called at runtime,
but it gains the ability to use non-executable language features
within it; for example, it can take parameters and return results of
non-executable types (such as `int` or `real`), and it can use
non-executable statements or expressions (such as quantifier
expressions or `obtain`). Here is an example of a ghost function:

```
ghost function collatz(x: int): int
    requires x > int(0);
{
    if x % int(2) == int(0) {
        return x / int(2);
    } else {
        return int(3) * x + int(1);
    }
}
```

This uses the infinite `int` type (which would not be permitted within
non-ghost code).

Finally, note that functions can be "generic". This is done by adding
one or more type variable names, enclosed in `< >`, after the function
name. For example:

```
function make_tuple<U, V>(x: U, y: V): {U, V}
    requires !allocated(x);
    requires !allocated(y);
{
    return {x, y};
}
```

In this case, the "type variables" `U` and `V` can stand for any valid
type.

When calling a generic function, the compiler will (in most cases)
automatically infer the required type parameters based on the types of
the actual arguments at the call site (or other surrounding context).
It is also possible to specify the type parameters explicitly at the
call site, if desired (as in e.g. `make_tuple<bool, i32>(true, 100)`).

Note the preconditions in the above example. When verifying the
function, the verifier needs to prove that the return value is not
allocated (this is a general rule -- return values must be
non-allocated -- see the description of the return statement above).
This would be fine if, say, the return type was `{i32, i32}`, but if
`U` and `V` were allocatable array types, say, then it might become a
problem. That is why the precondition is required -- effectively we
are shifting the burden onto the caller to prove that non-allocated
values are being passed for `x` and `y`. As long as this condition is
true, then the `return {x, y};` statement will be valid.


### Extern functions

A function can also be marked `extern`. In this case, it is illegal to
supply a function body. Also, an `extern` function (of a given name)
can occur in either the interface or implementation of a module, but
not both. Finally, note that a function cannot be both `extern` and
`ghost` at the same time.

An `extern` function represents a function defined in some external
environment, such as a separate C file which is linked into the
program externally. (The exact process for doing this is documented
elsewhere.)

The verifier will prove that all `requires` conditions on an extern
function are met at the call site(s), just as with normal functions.
But note that the verifier will *not* prove that the external
implementation respects any `ensures` conditions that are stated. For
example, in the following:

```
extern function foo(x: i32): i32
    requires x > 0;
    ensures 0 <= return <= 10;
```

the verifier will prove that, at all calls to `foo`, the value passed
for the `x` argument is positive; but, it will then just *assume* that
the external code (that implements the `foo` function) does indeed
return a value that is between 0 and 10. This latter fact is not
proved (nor can it be, because the Babylon compiler cannot see the
implementation code for the `foo` function). Thus, the use of
`ensures` conditions on `extern` functions can be considered similar
to the use of the `assume` statement; it introduces an assumption that
the verifier does not check. For that reason, such `ensures`
conditions should be used with caution and they should be audited
carefully to make sure that the external functions being used do
indeed comply with the assumptions being made.

Extern functions can also (optionally) have a separate "extern name"
specified, by writing an equals sign and a string after the function
declaration (but before any requires/ensures conditions). For example:

```
extern function foo() = "bar";
```

or

```
extern function foo(x: i32): i32 = "bar"
    requires x > 0;
    ensures return > 0;
```

In this case, the function will be referred to as `foo` in the Babylon
code, but will actually correspond to a function named `bar` in the
external environment (e.g. a C function named `bar`). This can
sometimes be useful e.g. if you have C functions with complicated
names (or with lengthy "prefixes" etc.) and you want to use simplified
versions of those names on the Babylon side.

Note that all extern names must consist only of alphanumeric
characters or underscores, and begin with an alphabetic character.


# "Memory leak" prevention

Certain values in the language represent "pointers" to allocated
memory. For example, the allocatable array type `T[*]` (where T is any
type) can be thought of as a pointer to a heap-allocated array of "T"
values. It is obviously important that this memory be "freed" once the
program is no longer using it.

The way this is handled is that the language first of all arranges
that all such "allocated" values will be stored in local variables of
some function or other. And secondly, the verifier checks that,
whenever a local variable `v` goes out of scope, the condition
`allocated(v)` is false (in other words, `v` does not contain any
pointer to any memory that needs to be freed).

The following example illustrates this:

```
// Assume the following functions are defined externally somewhere.

// alloc_array(A, N) will "resize" the array A to have N elements (allocating memory if needed).
extern function alloc_array<T>(ref A: T[*], N: u64);
    requires forall (x: T) !allocated(x);
    requires sizeof(A) == 0;
    ensures sizeof(A) == N;
    
// free_array(A) will free the memory for array A, resizing it to have zero elements.
extern function free_array<T>(ref A: T[*]);
    requires forall (x: T) !allocated(x);
    requires sizeof(A) > 0;
    ensures sizeof(A) == 0;

// Here is a function that allocates some memory:
function test(b: bool)
{
    var x: i8[*];
    alloc_array(x, 10);

    if b {
        var y: i32[*];
        alloc_array(y, 10);

        // At this point, y is going out of scope so the verifier will try to prove
        // "!allocated(y)". But this will fail because allocated(y) is true (because
        // sizeof(y) is not zero). So the memory leak will be caught (if the program
        // is verified).
    }

    free_array(x);

    // At this point, sizeof(x) is zero, and hence allocated(x) is false.
    // The verifier will be able to prove this, since it can see the postcondition
    // on free_array<T>. Therefore, no error regarding x will be reported
    // (as expected).
}
```

In addition, the language ensures that "allocated" values cannot
appear on the right-hand-side of assignment statements. This means
that code like `a = b;` (where `a` and `b` are both allocated arrays)
is not allowed; this not only prevents the previous contents of `a`
being leaked, but it also prevents a situation where `a` and `b` are
both aliases for the same piece of allocated memory (which might e.g.
result in a "double-free" bug if `a` and `b` are both freed later on).


# Modules

As noted previously, a module is, effectively, the "outermost"
structuring mechanism of the Babylon language. A Babylon program is a
collection of modules (perhaps linked with some external C code, if
"extern" functions are being used) and each module corresponds exactly
to one Babylon source code file on disk.

A module is, in essence, a set of declarations. Declarations can be
listed in any order; the compiler will automatically sort them into
dependency order if needed. (As noted under "Declarations" above,
circular or recursive dependencies between declarations are not
currently permitted.) The declarations are also divided into two
sections: interface and implementation. Any declarations mentioned in
the "interface" section are visible to other modules (should they
choose to import this module); declarations listed in the
"implementation" section are not. (It's also possible for declarations
to appear in both interface and implementation -- generally there will
be an "abbreviated" form in the interface and a "full" version in the
implementation -- the exact rules for this are described under
"Declarations" above.)

The syntactic structure of a module is as follows:

```
// The module name comes first:
module <module-name>

// Any imports needed by the interface are listed here (there can be
// zero or more imports):
import <module-name>;
import <module-name>;
...

// Now the module interface appears, like this:
interface {
    // Zero or more declarations (functions, types, etc.) can appear here:
    <declaration>
    <declaration>
    ...
}

// Next we list any imports (zero or more) needed by the implementation:
import <module-name>;
import <module-name>;
...

// Finally we give the actual implementation declarations (zero or
// more):
<declaration>
<declaration>
```

A <module-name> consists of one or more identifiers, separated by
dots. For example, `Hello` and `Algorithms.Sort.Quicksort` are valid
module names. (It is conventional, but not required, for module names
to begin with a capital letter.)

There are actually multiple forms of the "import" directive. The
outline above only showed the basic form which is `import
<module-name>;`. If this is used, then any function, constant, or type
declared in the "interface" section of the imported module will be
visible in this module, under its own (unqualified) name. For example,
if we use `import MyModule;` and `MyModule` includes `function
foo(...)` in its interface, then the name `foo` will, from now on,
refer to the function `foo` exported by `MyModule`.

If two or more imported modules happen to export the same name, then
that is not itself an error, but any attempt to use that name will
result in an "ambiguity" error (at compile time). For example, if
modules A and B both export a function named `foo`, and we have
`import A; import B;` in our module, then every time we try to
reference `foo` in our module, this will be an error (because `foo`
could refer to either `A.foo` or `B.foo`).

Note that type names and function/constant names form two different
"namespaces" or "groups" of names. So if (continuing the same example)
module A exported a type named `xyz`, and module B exported a function
named `xyz`, then there would be no conflict, because for any given
usage of the name `xyz`, the context will tell us whether a type
(`type` or `datatype` declaration) or a value (`function` or `const`
declaration) is being referenced. It is only if two types, or two
values, have the same name, that a problem results.

To solve the ambiguity problem it is also permitted to refer to
imported items via their "fully qualified" name. For example, if we
have `import A; import B;` and both `A` and `B` export a function
named `foo`, then we can always write `A.foo` to refer to the "foo"
function from module A, or `B.foo` to refer to the "foo" function from
module B. (As explained above, writing just `foo` would be ambiguous
in this case.)

The second form of the import statement adds the word `qualified`
immediately after `import`. For example, `import qualified M;`. This
makes it so that any names imported from module M *must* be referred
to using their fully qualified names. For example, if `M` exports a
function `foo`, then it is no longer possibly to refer to that
function simply as `foo`; one has to write `M.foo` instead.

The third form of the import statement is `import qualified
<module-name> as <name>;`. This is similar to `import qualified`
except that an alternative name is used to refer to the module. For
example, if we write `import qualified MyModule as M;`, and if
MyModule exports a function named `foo`, then we now have to refer to
that function as `M.foo`. The names `foo` or `MyModule.foo` cannot be
used in this case.

It is also possible to use `as` without `qualified`. For example, one
could write `import MyModule as M;`. This would import all the names
from `MyModule` as unqualified names, but also allow them to be
explicitly qualified as `M.some_name` (instead of the usual
`MyModule.some_name`), if desired.

Here is a complete (fairly minimal) example of a module. It exports a
single function named "hello" which prints "Hello World!" when called.
(It assumes that another module "Console" containing a function
"println" is available.)

```
module Hello

interface {
    function hello();
}

import qualified Console as Con;

function hello()
{
    Con.println("Hello World!");
}
```

## Dotted Module Names

It is possible to include dots in a module name. For example, you
could have a module named `Foo.Bar`. An imported item from this module
might be referred to as `some_name` (unqualified) or
`Foo.Bar.some_name` (qualified).

As explained in the [Babylon Package System](package.md) document,
dots in module names correspond to subdirectories on disk. For
example, the `Foo.Bar` module would be located in a file `Foo/Bar.b`
on disk.


# Additional Syntax Rules

This section gives some further details about the syntax rules of the
language, which did not fit anywhere else.

## Restrictions on short-cut function syntax

Recall that a "short cut" function call syntax, in which a single
tuple or record argument can be passed to a function without using
parentheses, as in `f{1,2,3}` for example, is available. 

Due to parsing limitations, that syntax *cannot* be used *immediately*
after one of the following keywords:
 - `match`
 - `assert`
 - `while`
 - `if` (when used as a statement)
For example, `if f{1} { return; }` is not a valid statement. The
alternative form `if f({1}) { return; }` could be used instead. The
formulation `if (f{1}) { return; }` would also be acceptable (in this
case, the function call is not *immediately* after the `if` keyword --
due to the intervening `(` character -- which is why it is allowed).

## Comma-separated lists

All comma-separated lists may contain a final trailing comma. For
example, `f(1,2,)` is a valid function call expression. Similarly,
`{x: i32, y: i32,}` is a valid record type.

This is sometimes useful when formatting long type declarations over
multiple lines, for example:

```
type MyRecord = {
    a: i32,
    b: i32,
    c: i32,
};
```

## Empty statements

An empty statement (i.e. a lone `;`) is allowed anywhere that a
statement would be permitted. Such a statement does nothing at runtime
(it is just skipped over).

## Parenthesized patterns

When writing patterns (for `match` expressions or statements), it is
permissible to enclose a pattern in parentheses. This does not change
the meaning of the pattern. For example, `match x { case (1) => ... }`
is functionally the same as `match x { case 1 => ... }`.

## Parsing of qualified ("dotted") names

Sometimes when using qualified names, ambiguity may result because of
an object in scope with the same name as the module.

For example, in the following:

```
import qualified Foo;  // assume Foo exports a constant named 'x'

const Foo = {x = 1};

const ABC = Foo.x;   // error
```

the final expression `Foo.x` is ambiguous, because it could refer to
either the `x` object exported from the `Foo` module, or the `x` field
of the `Foo` record defined in this module.

If the `x` field of the `Foo` record was intended, one workaround
could be to add parentheses, as in: `(Foo).x`. (A parenthesized name
like `(Foo)` cannot form part of a qualified name, so `(Foo).x` cannot
be interpreted as referring to some object `x` exported from a module
`Foo`; instead it is interpreted as accessing a field `x` from some
object `Foo` in the current module.)

If the `x` name from the `Foo` module was intended, then the best
solution would be to give a new name to the `Foo` module using the
`as` syntax. For example, `import Foo as FooModule;` could be used.
Then, `x` could be referred to as `FooModule.x`.

Of course, a better solution might be to avoid the name clash in the
first place, i.e. do not create a global constant named `Foo` if you
already have a module named `Foo` in the program!

Note that different rules apply to *local* variable names (i.e.
variables defined within a function body, or function argument names).
A local variable will always *shadow* a module of the same name. For
example, in this code:

```
import qualified Foo;  // assume Foo exports a constant named 'x'

function f(): i32
{
    var Foo = {x = 100, y = 200};
    return Foo.x;   // ok
}
```

the reference to `Foo.x` is not ambiguous -- it refers to the local
variable `Foo` (created on the line above), and not the module `Foo`.
This is because the `Foo` variable is in an "inner" scope and
therefore shadows the corresponding module name from the "outer"
scope. If the name `Foo.x` from module `Foo` was wanted, then it would
be necessary to rename the local variable, to avoid the shadowing.
