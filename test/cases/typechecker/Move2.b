module Move2

interface {}

import Test;

function test1(): u64
{
    return sizeof(alloc_array<i32>(100));  // error, array not freed
}

function test2(): i32
{
    return {alloc_array<i32>(23), 45}.1;   // error, array not freed
}

function f(move x: i32): i32  // 'move' here is redundant, but accepted
{
    return x;
}

function test3(): i32
{
    var i = 100;
    var j = f(i);   // 'move' of i is ignored
    var k = f(i);   // i is still usable
    return j;
}

function test4(x: move i32[*])
{
    // error: x not freed
}

function test5(): i32
{
    var a: i32[*] = alloc_array(3);
    ref r = a;
    free_array(a);
    return r[0];   // error: the variable referenced by r has been freed.
}

function test6(b: bool)
{
    var a: i32[*] = alloc_array(10);
    while b {
        free_array(a);  // error, a moved if loop entered, but not if loop skipped
    }
}

function test7(b: bool)
{
    var a: i32[*] = alloc_array(10);
    while b {
        free_array(a);
        a = alloc_array(5);
        // this is ok because a is "re-filled" by the end of the loop
    }
    free_array(a);  // free a before returning
}

datatype Maybe<a> = Just(a) | Nothing;

function test8()
{
    var m: Maybe<i32[*]> = Just(alloc_array(10));

    var i = {Just(alloc_array<i8>(5)), 1234}.1;  // error: array leaked.
    
    match m {
    case Just(a) => free_array(a);
    }
}

function test9(move r: {a: i32[*], b: i32[*]})
{
    match r {
    case {a=a} =>        // error: b was not matched
        free_array(a);
    }
}
