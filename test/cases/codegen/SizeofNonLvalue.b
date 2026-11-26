module SizeofNonLvalue

// sizeof applied to expressions that are not lvalues, in executable code.
//
// This used to be a type error when the array type was allocatable (the
// worry was that the array would be "lost", and so never freed). It is now
// allowed: in executable code, an expression that is not an lvalue is never
// allocated (function results, and the results of if, match and let, are in
// "value positions"), so there is nothing to lose.

interface {
    function main();
}

import Test;

datatype Maybe<a> = Nothing | Just(a);

function make_array(): i32[*]
    ensures sizeof(return) == u64(0);
{
    var a: i32[*];
    return a;
}

function make_2d_array(): i32[*,*]
    ensures !allocated(return);
{
    var a: i32[*,*];
    return a;
}

function make_pair(): {i32[*], i32}
    ensures sizeof(return.0) == u64(0);
{
    var p: {i32[*], i32};
    return p;
}

function make_fixed(): i32[7]
{
    var a: i32[7];
    return a;
}

function main()
{
    // Function call results
    print_u64(sizeof(make_array()));
    var s: {u64, u64} = sizeof(make_2d_array());
    print_u64(s.0);
    print_u64(s.1);
    print_u64(sizeof(make_pair().0));
    print_u64(sizeof(make_fixed()));

    // if, let and match results
    var c = true;
    print_u64(sizeof(if c then make_array() else make_array()));
    print_u64(sizeof(let n = 1 in make_array()));
    var m: Maybe<i32> = Just(1);
    print_u64(sizeof(match m { case Just(_) => make_array()  case Nothing => make_array() }));

    // An lvalue still gives the current size
    var a: i32[*];
    alloc_array<i32>(a, 3);
    print_u64(sizeof(a));
    free_array<i32>(a);
    print_u64(sizeof(a));
}
