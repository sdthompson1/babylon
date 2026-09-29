module MatchAllocExpr

// In a match *expression*, a pattern variable is never a copy of the
// matched value (it just refers to part of the scrutinee). Therefore,
// an ordinary (non-ref) pattern variable may bind an allocated value.
// This test checks that such expressions compile and run correctly
// (in particular, nothing is copied or freed by the match).

// (In a match *statement* this is not allowed; see
// test/cases/verifier/MatchAlloc.b.)

interface {
    function main();
}

import Test;

datatype Maybe<a> = Nothing | Just(a);

function payload_size(m: Maybe<i32[*]>): u64
{
    return match m { case Just(a) => sizeof(a) case Nothing => u64(0) };
}

function payload_first(m: Maybe<i32[*]>): i32
{
    return match m {
        case Just(a) => if sizeof(a) > u64(0) then a[0] else -1
        case Nothing => -2
    };
}

function record_size(ref r: {i32[*], i32}): u64
{
    return match r { case {a, _} => sizeof(a) };
}

function main()
{
    var empty: i32[*];
    var m: Maybe<i32[*]> = Just(empty);
    match m {
    case Just(ref p) =>
        alloc_array<i32>(p, 5);
        p[0] = 42;
    case Nothing =>
    }

    var n1 = payload_size(m);
    print_u64(n1);
    var x1 = payload_first(m);
    print_i32(x1);

    var n2: u64 = match m { case Just(a) => sizeof(a) case Nothing => u64(0) };
    print_u64(n2);

    // The array is still there afterwards
    match m {
    case Just(ref p) =>
        print_i32(p[0]);
        free_array<i32>(p);
    case Nothing =>
    }

    var n3 = payload_size(m);
    print_u64(n3);
    var x3 = payload_first(m);
    print_i32(x3);

    var none: Maybe<i32[*]> = Nothing;
    var n4 = payload_size(none);
    print_u64(n4);
    var x4 = payload_first(none);
    print_i32(x4);

    // Allocated field of a record
    var r: {i32[*], i32} = {empty, 1};
    alloc_array<i32>(r.0, 3);
    var n5 = record_size(r);
    print_u64(n5);
    print_u64(match r { case {a, _} => sizeof(a) });
    free_array<i32>(r.0);
}
