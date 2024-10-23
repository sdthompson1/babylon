module Move

// Various tests of "move semantics"

interface {}

import Test;

type MyRecord = { x: i32[*], y: i32[*] };

function f(arr: ref  i32[*],
           rec: move MyRecord): i32
    requires sizeof(arr) > 0;
{
    match rec {
    case {x=x, y=y} =>
        free_array(x);
        free_array(y);
        return arr[0];
    }
}

function test1()
{
    var rec: MyRecord = { x = alloc_array<i32>(10),
                          y = alloc_array<i32>(20) };
    var n = f(rec.x, rec);   // error: 'rec' moved, so can't use rec.x as the 1st arg.
}

function test2(move m: MyRecord)
{
    match m {
    case {x=x, y=y} =>
        free_array(y);
        // error: x dropped
    }
}

datatype Maybe<a> = Just(a) | Nothing;

function test3(move m: Maybe<i32[*]>): i32
{
    return match m {
    case Just(a) => a[0]   // error: a dropped
    case Nothing => 0
    };
}

function test4(move m: {i32[*], bool}): i32[*]
{
    return match m {
    case {a, b} => a  // ok, a is moved
    };
}

function test5(b: bool): i32[*]
{
    var a1: i32[*];
    var a2: i32[*];
    if b {
        return a1;   // error: a2 dropped
    } else {
        free_array(a2);
    }
    // error: only a1 moved on one branch, only a2 on the other
    // (for simplicity, the typechecker doesn't look at whether each branch returned
    // or not - for now at least.)

    return a1;  // ok because typechecker assumes "else" branch was followed in this case
}

function test6(move m: MyRecord, move b: i32[*])
{
    var a = m.x;   // error: move from part
    free_array(m.y); // error: move from part

    test2(m);    // empties m
    m.x = b;     // error: moving to part of an object
}

function test7(move x: {i32[*], i32[*]})
{
    match x {
    case {ref a, b} =>  // Error - this tries to copy 'b', but it does not have Copy trait.
        a[0] = 0;  // fine, 'a' is modifiable reference
        b[0] = 0;  // fine, 'b' is a normal variable (or would be, if we could have copied it)
        free_array(a);  // error, cannot move from reference
        free_array(b);  // fine, 'b' is a normal var and we can move from it

        // error, 'x' was not dropped (as the match was by reference)
    }
}

function test8(move x: MyRecord)
{
    test2(x);
    test2(x);  // error: x already moved
}

function test9(move m: MyRecord, move a: i32[*]): MyRecord
{
    return {m with x=a}; // error, discards old value of m.x
}

function test10(move m: MyRecord)
{
    match m {
    case {x=x, y=_} =>  // error: discards m.y
        free_array(x);  // ok
    }
}

function test11(move m: MyRecord[*])
{
    var a = m[0];  // error: moving part of array  (also: m not freed)
}

function test12(move m: MyRecord): MyRecord
{
    var x = m;   // m now empty, x full
    var y = x;   // x,m now empty, y full
    m = y;       // x,y empty, m full
    return m;    // All variables now empty.
}

function test13(): i32
{
    var a = alloc_array<i32>(10);
    return 99;
    // error: 'a' leaked
    // (should only be reported once)
}

function test14(x: bool)
{
    var a: i32[*];
    var b: i32[*];
    
    var f: i32[*];
    free_array(f);
    
    if x {
        f = a;
        b[0] = 1;   // modify 'b' on this code path
    } else {
        f = b;
    }
    // error: a moved on one branch; b on the other.

    free_array(f);  // avoid other errors
    free_array(a);  // avoid other errors
}

extern type NoMove;

function test15(move x: NoMove) {}  // error: can't move x

function test16(move x: i32[*], move y: i8[*]): {i32[*], i8[*]}
{
    return {x, y};  // ok
}

function test17(move x: i32[*], move y: i8[*]): i32[*]
{
    return {x, y}.0;  // error: 'y' was not freed.
}

ghost function test18(): i32[*]
{
    var x: i32[*] = alloc_array(10);
    var y: i8[*] = alloc_array(12);
    return {x, y}.0;   // ok in ghost context
}

ghost function test19(move x: i32[*])   // error: move doesn't make sense for ghost calls
{}

ghost function test20(ref m: MyRecord, b: i32[*])
{
    // Similar to test6, but ghost code so the errors don't arise
    var a = m.x;  // ok
    free_array(m.y);  // ok (does nothing)
    test2(m);   // ok (does nothing)
    m.x = b;    // ok
}
