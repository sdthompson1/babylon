module ConstRef

interface {}

import Test;

const c: i32 = 100;

function f1()
{
    ref r = c;
    r = 200;   // error, writing to read-only 'c' via reference 'r'
}

function f2()
{
    match (c) {
    case ref r =>  // this is ok, we are allowed to take a "const" ref to c
        var z = r + 1;   // reading 'r' is ok
        r = 99;          // error, writing 'r' is not ok
    }

    match (1 + 2) {
    case ref r =>    // this is now ok; lifetime of (1+2) temporary is extended to match lifetime of r.
    }
}

function foo(i1: i32,  i2: i32,  ref i3: i32)
{
}

function f3()
{
    var a = 1;
    var b = 2;

    foo(1+2, 3, a);  // ok, passing rvalue for normal argument is allowed
    foo(1, 2, a+b);  // error, passing rvalue for ref argument is not allowed
}
    

// Writability of formal arguments
function test_readonly(i: i32,       x: i32[],
                       ref j: i32,   ref y: i32[])
{
    i = 0;      // error, non-ref arg, cannot be written
    x[0] = 0;   // error, non-ref arg, cannot be written

    j = 0;      // ok, ref args can be written
    y[0] = 0;   // ok, ref args can be written
}
