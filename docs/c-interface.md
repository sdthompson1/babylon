
# Babylon/C Interface Guide

Stephen Thompson, February 2025

This document explains how the Babylon and C languages can be used
together. For example, it describes how Babylon's data structures are
laid out in memory, and how Babylon's `extern` function declarations
map on to C function prototypes. This information will be useful for
anyone wanting to call C functions from Babylon code, or vice versa.


# Introduction

The Babylon programming language supports calling external C functions
from a Babylon program. The Babylon program must declare an `extern`
function with the correct signature, and then a separate C
implementation must be provided (either by writing it directly in a
`.c` file, or by linking with an appropriate library that provides the
function).

The reverse -- calling Babylon functions from C -- is also possible,
although this is slightly more difficult because it requires knowing
the "name mangling" conventions used by the Babylon compiler.

Either way, successfully calling C code from Babylon, or vice versa,
depends crucially on knowing various details, such as how Babylon
types are represented in C, how Babylon function declarations map to C
function prototypes, and so on. The purpose of this document is to
explain all of these details.


# Data Formats

The first thing to do is explain how the different Babylon data types
are represented and accessed in C code.

The Babylon types are divided into two classes: "scalars" and
"aggregates". Scalars include `bool` and the eight built-in integer
types (`i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32` and `u64`). Any
"extern" types defined by the programmer (as in `extern type Foo;`)
are also considered scalars. All other types are considered
aggregates.


## Scalar types

A Babylon scalar type is directly represented by a C type according to
the following table:

| Babylon type | C type     |
| ------------ | ---------- |
| `i8`         | `int8_t`   |
| `i16`        | `int16_t`  |
| `i32`        | `int32_t`  |
| `i64`        | `int64_t`  |
| `u8`         | `uint8_t`  |
| `u16`        | `uint16_t` |
| `u32`        | `uint32_t` |
| `u64`        | `uint64_t` |
| `bool`       | `uint8_t`  |
| Extern type  | `void *`   |

(Note that the Babylon compiler assumes that the fixed width integer
types from `<stdint.h>` are available on the target platform and C
compiler.)

For the `bool` type, Babylon's `true` maps to `1` as a `uint8_t`, and
Babylon's `false` maps to `0`. (Babylon `bool` values should not be
set to a value other than `0` or `1` by C code, as this might cause
unpredictable results.)

For Babylon "extern types", the Babylon language does not assign any
particular interpretation to the actual value of the `void *` pointer.
The only time Babylon creates values of "extern" types is if a
"default" variable of such a type is created (as in `var v: Foo;`). In
this case, the `void *` is set to NULL (assumed to be an all-zero bit
pattern). The only other way to create values of extern types is via C
code, and in this case Babylon just copies around the `void *` value
that it receives from C as an opaque pointer; in particular, it does
not ever dereference this pointer.


## Aggregate types

An aggregate type is always represented by a `char[]` array of an
appropriate size. The start address of this array need not have any
particular alignment.

We describe each of the possible aggregate types in turn.


### Records

A Babylon record is a `char[N]` array where N is the sum of the sizes
of the individual record fields. The record fields are simply
`memcpy`-d into the char array, in order, with no padding between
them. (In other words, Babylon uses a "packed" record representation.)

For example, the Babylon record type `{a: u8, b: i32, c: bool}` is
represented in C as a `char[6]` array, where the first byte
corresponds to `a`, the next four bytes to `b`, and the final byte to
`c`.

Remember that the start address of the record need not be aligned, and
also (as mentioned) there is no alignment padding, so typically it is
necessary to use `memcpy` to read values out of, or put values back
into the `char[]` array. For example, to read the contents of the `{a:
u8, b: i32, c: bool}` record mentioned above, the following C code
might be used:

```
char *p = ...; // Assume this points to the char[6] for the Babylon record.

uint8_t a;
memcpy(&a, p, 1);   // Extract 'a' (first byte) from the record.

int32_t b;
memcpy(&b, &p[1], 4);  // Extract 'b' (next four bytes) from the record.

uint8_t c;   // Bool in Babylon is uint8_t in C
memcpy(&c, &p[5], 1);  // Extract 'c' (final byte) from the record.
```

Alternatively, if you know that your target platform supports
unaligned memory accesses, then something like the following may be
possible:

```
char *p = ...;  // The same record pointer as before

// Warning: this code might not work on all platforms!
uint8_t a = *(uint8_t*)p;          // Directly access field 'a'
int32_t b = *(int32_t*)(&p[1]);    // Directly access field 'b'
uint8_t c = *(uint8_t*)(&p[5]);    // Directly access field 'c'
```

However, note that this method is not compliant with the C standard
(because of the unaligned memory access), so it should only be used if
you are certain that it will work on your particular platform and
compiler.

Note also that whenever the Babylon compiler needs to generate C code
for accessing records, it will always use the `memcpy` method, since
this is guaranteed to work on all platforms (and compilers are usually
good at optimizing away the `memcpy` calls). Hence, if you look at the
C code generated by the Babylon compiler, you will often see a lot of
`memcpy` or `memmove` calls!


### Datatypes

A Babylon datatype is represented as a "tag" (either a 1, 2 or 4 byte
unsigned integer), followed by the "payload" of the datatype
immediately afterwards (with no padding).

The tag indicates which data constructor was used to construct this
particular datatype value. The constructors are numbered sequentially,
starting from 0, in order of their appearance in the datatype
declaration.

The tag is only as big as it needs to be to represent all of the
constructors; this means that most datatypes (those with 256 or fewer
constructors) will use a single byte tag, but larger datatypes may use
2 or even 4 bytes for the tag.

For example, the following datatype:

```
datatype Foo = Foo | Bar(u32) | Baz{x: i32, y: i32}
```

might be represented by the C declaration `char a[9];`. The first byte
of this array (`a[0]`) is the tag; this is either 0, 1 or 2. If the
tag is 0 (signifying a `Foo` value) then the rest of the array bytes
go unused. If the tag is 1 (signifying a `Bar`) then the next 4 bytes
(`a[1]` to `a[4]`) are a `uint32_t` value, memcpy'd into place,
representing the `u32` payload. If the tag is 2 (signifying a `Baz`)
then the next 8 bytes (`a[1]` to `a[8]`) are the representation of the
record; in other words, `a[1]` to `a[4]` correspond to an `int32_t`
for the `x` value, and `a[5]` to `a[8]` are another `int32_t`
corresponding to `y`.


### Fixed-sized arrays

Fixed-sized arrays in Babylon (such as `i32[10]`) are represented as a
`char[N]` array where N is the size of the element type (in bytes)
multiplied by the number of elements. The elements are simply laid out
in memory in order, with no padding between them, as one might expect.

If the array is multi-dimensional then the array is laid out in memory
in "Fortran order" rather than "C order". What this means is that the
left-most index is the most rapidly varying, as one advances through
memory. For example, an array `a` of Babylon type `i32[3,2]` would be
laid out in memory in the order: `a[0,0]`, `a[1,0]`, `a[2,0]`,
`a[0,1]`, `a[1,1]`, `a[2,1]`. The array would occupy a total of 24
bytes (4 bytes for each element times 6 elements in total). Similar
principles apply to three and higher dimensional arrays.


### Allocatable and incomplete arrays

Allocatable arrays (`T[*]`) and incomplete arrays (`T[]`) are a little
more complicated. These are represented __indirectly__ as a
descriptor. The first P bytes (where P is the pointer size, e.g. 8 for
a 64-bit system) are a pointer to the array itself, which is
represented exactly as described above for fixed-sized arrays. The
next 8 bytes are the number of elements in the first dimension (as a
`uint64_t`), then the next 8 bytes are the number of elements in the
second dimension, and so on. The total size of the descriptor is `P +
8*n` where P is the pointer size and n is the number of dimensions.

The only difference between allocatable and incomplete arrays is that
for an allocatable array, it is permissible to modify the descriptor
(for example, reallocating the array by changing the pointer to point
somewhere else would be permitted), but for an incomplete array, the
descriptor must be treated as read-only (although the actual array
elements could still be changed if desired).

For example, if (in C) you had a `char *p;` referring to the Babylon
type `i32[*]`, and you wanted to access the element of this array at
index 3, you might do something like:

```
char *data;
memcpy(&data, p, sizeof(char*));  // 'p' is not necessarily aligned, so use memcpy.

int32_t value;
memcpy(&value, data + 3 * 4, 4);  // 'data' is not necessarily aligned either. 4 = sizeof(int32_t).
```

Note that the Babylon language itself does not specify anything about
how the array memory is to be allocated. However, the "alloc"
functions in the `Array` module of the `coretypes` package (provided
with the compiler) will allocate this memory using `malloc` (actually
`calloc` to be precise), and free it using `free`. It is expected that
most Babylon programs will follow this convention, although it is
certainly possible to replace the `Array` module with a different
implementation (using e.g. a custom memory allocation strategy) if
this is desired.


## Abstract types

Recall that in Babylon types can sometimes be "abstracted" by a module
interface. For example, in the following module:

```
module AbstractTypeDemo

interface {
    type Foo;
}

type Foo = i32;
```

the type `Foo` is an "abstract type". In particular, any importer of
`AbstractTypeDemo` would see a type `Foo`, but they would not know
anything about its representation or internal structure. The reader
may be wondering how the Babylon compiler handles this situation.

The answer is that, currently, the Babylon compiler is a "whole
program compiler", which means that it is able to look into the full
definition (not just the interface) of any module at any time.
Therefore, if at any time the compiler needs to know the C
representation of the `Foo` type, it can just look directly at the
`AbstractTypeDemo` implementation and see that (in this case) `Foo` is
just a synonym for `i32`, so its representation in C is just
`int32_t`.

The implication of this for C programmers is that no special handling
is required for these abstract types. The C representation of an
abstract type corresponds directly to the representation of its
concrete implementation type, according to the rules described above.
This does mean that the "abstractness" of a type is lost when going to
C -- i.e., the implementation of the type is not "hidden" from the C
code, as one might have liked -- but given the current way that the
compiler works, this is unavoidable. (Perhaps a future Babylon
compiler will offer alternative ways of representing abstract types,
e.g. as a `void *` pointer or something similar, but at present there
are no plans to implement anything like that.)


# Calling C Functions from Babylon

To call a C function from Babylon, on the Babylon side, one must make
an `extern` function declaration, such as `extern function foo(x:
i32): i32;`. One must then define the corresponding function in C (in
this example, a C function with prototype `int32_t foo(int32_t x);`
would be defined) and arrange for this C function to be included in
the final program.

In this section, we discuss how the Babylon `extern` declaration is
mapped to a C function prototype.

First of all, the name of the C function is equal to the name used in
the `extern` declaration on the Babylon side, except where an "extern
name" was explicitly given in the Babylon code, in which case that
name is used instead. For example, `extern function foo();` in Babylon
corresponds to a C function named `foo`, but `extern function foo() =
"bar";` corresponds to a C function named `bar`.

Secondly, each parameter of the Babylon function maps to a
corresponding parameter of the C function. For non-`ref` scalar types,
the C parameter just has the appropriate C type, according to the
table of scalar types given above (e.g. `i32` becomes `int32_t`,
`bool` becomes `uint8_t`, etc.). For scalar `ref` types, the C
parameter is a `char *` pointing to an in-memory representation of the
scalar (i.e. the `int32_t` or whatever value, but memcpy'd into the
given `char *` address). Note that this pointer need not necessarily
be aligned, even if values of that scalar type would normally be
aligned. Finally, for aggregate types (whether `ref` or not), the C
parameter is a `char *` pointing to the in-memory representation of
the aggregate (as described above).

For the return value: If the Babylon function doesn't declare a return
value then the C function returns `void`. If the Babylon function
returns a scalar type, then the return type of the C function is the
corresponding C type. Finally, if the Babylon function returns an
aggregate, then the C function returns `void` but there is an extra
parameter (coming first in the list) of type `char *`. The C function
is expected to write its return value into the address pointed to by
this extra parameter.

Any pre or post conditions of the `extern` declaration are simply
ignored when determining the form of the C prototype.

Here are some examples:

(1) The Babylon declaration `extern function say_hello();` might be
implemented by the following C function:

```
void say_hello()
{
    printf("Hello, world!\n");
}
```

(2) A function `extern function foo(x: i32, y: i32): {i32, i32};`
could be implemented as follows:

```
void foo(char *ret, int32_t x, int32_t y)
{
    memcpy(ret, &x, sizeof(int32_t));
    memcpy(ret + sizeof(int32_t), &y, sizeof(int32_t));
}
```

This would have the same effect as the Babylon function:

```
function foo(x: i32, y: i32): {i32, i32}
{
    return {x, y};
}
```

(3) A function

```
extern function foo(ref x: i32, y: i32): i32 = "bar"
    requires x < I32_MAX;
    requires y < I32_MAX;
    ensures x == old(x) + 1;
    ensures return == y + 1;
```

might be implemented as:

```
int32_t bar(char *x, int32_t y)
{
    int32_t x_value;
    memcpy(&x_value, x, sizeof(int32_t));
    x_value++;
    memcpy(x, &x_value, sizeof(int32_t));
    return y + 1;
}
```

Note that it is the responsibility of the C programmer to verify that
their implementation does indeed satisfy any `ensures` conditions
stated in the Babylon extern declaration. These will not be verified
(nor can they be, since the Babylon compiler has no way to verify C
code). The Babylon compiler will however verify that any `requires`
conditions are complied with at all applicable call sites in the
Babylon code.


## Generic Functions

Generic functions require special handling. Parameters of generic type
are treated as if they were aggregates, i.e. they are represented on
the C side by a `char *` pointing to a block of memory containing the
generic value. In addition, every generic function will receive one
extra `uint64_t` parameter (after the "return value" argument if any,
but before the normal function arguments) giving the size, in bytes,
of that generic type.

For example, `extern function foo<T>(x: T)` will be represented in C
as `void foo(uint64_t size, char *x);` where `size` is the size in
bytes of a `T` object, and `x` is the pointer to the `T` argument
passed in the call.

As another example, the following function:

```
extern function permute<T, U>(x: {i16, T, U}): {U, i16, T}
    requires !allocated(x);
    ensures !allocated(return);
```

might be implemented in C as:

```
void permute(char *ret, uint64_t T_size, uint64_t U_size, char *x)
{
    memcpy(ret, x + 2 + T_size, U_size);
    memcpy(ret + U_size, x, 2);
    memcpy(ret + U_size + 2, x + 2, T_size);
}
```

Note the use of `requires !allocated(x);` which ensures that the `T`
and `U` values passed to the function do not contain any pointers to
allocated memory or similar. This is what makes it permissible to use
`memcpy` to copy the `T` and `U` values around within the function.


# Calling Babylon Functions from C

Each function in the interface of a Babylon module corresponds
directly to a C function, and can be called from C code if desired.
The Babylon function declaration is mapped to a C function prototype
exactly as described in the "Calling C Functions from Babylon" section
(above). The only difference between the two cases (calling C from
Babylon, or calling Babylon from C) is in the naming of the functions.
Because two different Babylon functions, in different modules, can
legally share the same function name, there needs to be a way to
differentiate between these on the C side. The solution employed is to
use a "name mangling" scheme.

To convert a Babylon function name to C, the compiler constructs the
"full name" of a function by concatenating the package name, a slash,
the module name, a dot, and the function name (in that order). (See
[Babylon Package System](package.md) for the definition of a
"package".) The resulting full name is then "mangled" by applying the
following transformations:

 - `.` is converted to `z_`.
 - `/` is converted to `zs`.
 - A leading `_` is converted to `zu` (any other underscore is left
   unchanged).
 - `-` is converted to `zm`.
 - `z` is converted to `zz`.
 - Any other character is left unchanged.

For example, suppose the following module was part of a package named
`test-package`:

```
module Foo.Bar

interface {
    function foo(x: i32);
    function my_function(): bool;
}
```

The "full names" of the functions (in the above sense) would be
`test-package/Foo.Bar.foo` and `test-package/Foo.Bar.my_function`, and
the corresponding C prototypes (after name mangling) would be:

```
void testzmpackagezsFooz_Barz_foo(int32_t x);
uint8_t testzmpackagezsFooz_Barz_my_function();
```

If instead the package name began with an underscore, e.g.
`_test_package`, then the prototypes would be:

```
void zutest_packagezsFooz_Barz_foo(int32_t x);
uint8_t zutest_packagezsFooz_Barz_my_function();
```

(This illustrates how the name mangling scheme avoids creating C
functions whose names begin with underscores -- this is important
because such names are reserved by the C standard and should not be
used by "user" code.)

Also note that the Babylon compiler, when run in `bab compile`, `bab
translate` or `bab build` mode, outputs a C header file for each
Babylon module involved in the build. (Look in the `build/c/`
directory under the root package of the build.) These header files are
useful because they contain compiler-generated C function prototypes
for all relevant Babylon functions. Therefore, there is no need to
actually perform the above name mangling or argument transformations
"by hand"; instead, you can either just `#include` the relevant header
file(s) directly into the build, or else, you can copy and paste the
necessary function prototypes into your C source code. You will then
be able to call the desired Babylon functions from C code without
needing to write out the function prototypes "manually". (You will
still have to write out the mangled names in full every time you want
to call the function, of course. If this becomes too burdensome, then
creating small helper functions, or using `#define`, might be
worth considering.)


# Accessing Babylon Constants from C

Programmers might also occasionally wish to access constants declared
in Babylon modules (via `const` declarations) from C code.

For constants of scalar type, this is straightforward. The Babylon
constant corresponds directly to a C `const` variable of global scope.
The name is mangled in the same way as for Babylon functions (see
previous section). For example, if package `test-package` contains:

```
module MyModule

interface {
    const c: u32 = 100;
}
```

then the constant `c` could be accessed from C using the following
prototype:

```
extern const uint32_t testzmpackagezsMyModule_c;
```

(Once again, this prototype could be found in the compiler-generated
header file, `MyModule.b.h` in this case, which might be preferable to
writing out the prototype by hand.)

For constants of aggregate type, things are slightly more complicated.
In this case the Babylon compiler will generate a __function__ that
returns a pointer to the aggregate data. For example, if `MyModule`
also contained:

```
const x: {i32, i32} = {10, 20};
```

then the corresponding C prototype would be:

```
char * testzmpackagezsMyModulez_x();
```

Calling this function would return a pointer to a static memory area
containing the value of the `x` constant (i.e. in this case it would
be a pointer to an eight byte memory area, consisting of the values 10
and 20, as four-byte signed integers, one after the other).

The function is constructed in such a way that the result of the call
is cached, so the first call may do some work building the aggregate
value in memory, but subsequent calls will just quickly return a
cached pointer. (A static `initialized` flag within the function keeps
track of this.)

Note that even though the returned `char *` pointer is not explicitly
marked as `const`, it should always be treated as if it was `const`,
and the data that it points to should never be modified. (Doing so
would amount to changing the value of a Babylon `const` variable at
runtime, which would have unpredictable and undesirable consequences.)


# Conclusion

Using the information and techniques described above, it is possible
to call C functions from Babylon code, call Babylon functions from C
code, and/or read the value of Babylon constants from C code.

For examples of these techniques in action, try looking at some of the
packages included with the Babylon compiler. For example, the `Array`
module in the `coretypes` package includes external C code for
allocating and freeing arrays. The `datetime` package includes C
functions for reading the system clock or sleeping for a given amount
of time. For a more complex example, the `gfx-engine` package shows
how to interface with the SDL library to make a simple graphics
engine.
