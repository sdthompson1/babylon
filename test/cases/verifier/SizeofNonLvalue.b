module SizeofNonLvalue

// sizeof of an expression that is not an lvalue is allowed in executable
// code, even if the array type is allocatable. (It used to be a type error,
// because the array would be "lost" and never freed.) Nothing can be lost,
// because a function cannot return an allocated array in the first place:
// the 'return' is a value position, and the verifier checks it.

interface {}

import Test;

function make_empty(): i32[*]
    ensures sizeof(return) == u64(0);
{
    var a: i32[*];
    return a;                             // OK, 'a' is not allocated
}

function make_allocated(): i32[*]
{
    var a: i32[*];
    alloc_array<i32>(a, 10);
    return a;                             // Error, copying an allocated array
}

function f1(): u64
    ensures return == u64(0);
{
    return sizeof(make_empty());          // OK
}

function f2(): u64
{
    return sizeof(make_allocated());      // OK here (the error is in make_allocated)
}

function f3(c: bool): u64
    ensures return == u64(0);
{
    var a: i32[*];
    return sizeof(if c then make_empty() else a);     // OK
}

function f4(c: bool): u64
{
    var a: i32[*];
    alloc_array<i32>(a, 10);
    var n = sizeof(if c then make_empty() else a);    // Error, copying an allocated array
    free_array<i32>(a);
    return n;
}

ghost function g1(a: i32[*]): u64
{
    return sizeof(if true then a else a);             // OK, ghost code
}
