module ValuePosAllocRun

// This program copies allocated arrays (by putting them in value positions),
// which is not allowed in executable code, so it must fail verification.
// See ValuePosAlloc.b for more info.

// If it were (wrongly) accepted, then it would read freed memory at runtime.
// Each of the functions below takes a by-value argument, and a 'ref' to an
// array which it frees. The verifier checks that a 'ref' argument does not
// alias any other argument, but a copy of the array, made in a value
// position, does not count as an alias. So the callee would free the array
// and then read it through the copy.

interface {
    function main();
}

import Test;

datatype Maybe<a> = Nothing | Just(a);

function free_then_read(p: i32[*], ref a: i32[*]): i32
    requires sizeof(p) == u64(3);
{
    free_array<i32>(a);
    return p[0];
}

function free_then_read_tuple(p: {i32[*], i32}, ref a: i32[*]): i32
    requires sizeof(p.0) == u64(3);
{
    free_array<i32>(a);
    return p.0[0];
}

function free_then_read_maybe(m: Maybe<i32[*]>, ref a: i32[*]): i32
    requires match m { case Just(p) => sizeof(p) == u64(3)  case Nothing => false };
{
    free_array<i32>(a);
    return match m { case Just(p) => p[0]  case Nothing => 0 };
}

function main()
{
    var a: i32[*];
    alloc_array<i32>(a, 3);
    a[0] = 1;
    var x = free_then_read(let n = 1 in a, a);    // Error, copying an allocated array
    print_i32(x);

    var b: i32[*];
    alloc_array<i32>(b, 3);
    b[0] = 2;
    var y = free_then_read_tuple({b, 1}, b);      // Error, copying an allocated array
    print_i32(y);

    var c: i32[*];
    alloc_array<i32>(c, 3);
    c[0] = 3;
    var z = free_then_read_maybe(Just(c), c);     // Error, copying an allocated array
    print_i32(z);
}
