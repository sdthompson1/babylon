module Arrays
interface {}

import Test;

function make_array(): i32[*]
{
    var a: i32[*];
    return a;
}

function f()
{
    var a: i32[*];
    resize_array<i32>(a, 100);
    
    var b: i32[*,*];
    resize_2d_array<i32>(b, 10, 10);

    var s: u64 = sizeof(a);    // OK
    var t: u64 = sizeof(b);    // Error, type mismatch
    var u: {u64,u64} = sizeof(b);    // OK
    
    var v = sizeof(make_array());         // Error, sizeof can only be used on lvalues
    ghost var g2 = sizeof(make_array());  // ... except in ghost code
    var w = sizeof(100);             // Error, sizeof can only be used on arrays
    var x = sizeof(1+true);          // Error, type mismatch. (sizeof a "bad" term)

    a[10] = 30;           // OK
    a[10] = true;         // Error, wrong type
    var i: i32 = a[10];   // OK
    var j: bool = a[10];  // Error, wrong type
    a[true] = 123;        // Error, wrong index type
    a[1,2] = 123;         // Error, wrong number of indexes

    b[1,2] = 30;          // OK
    var k: bool = b[2,3]; // Error, wrong type
    b[1] = 99;            // Error, wrong number of indexes
}

function f2(a: i32[*,*])
{
    var i = (1+true) [1];      // Error, type error in lhs of array projection
    var j = a [1,2+true];      // Error, type error in dimension
    var k = 1 [2];             // Error, cannot index "1"
}

function ref_not_allowed(a: i32[*],
                         b: {x: i32[4][*]})
{
    // Error, ref to resizable array element not supported (because the
    // array might be reallocated, therefore moving the element to a
    // different address in memory!)
    ref r1: i32 = a[10];

    // Similar error but the array is "buried" somewhere in the rhs expression
    ref r2: i32 = b.x[3][2];

    // A reference to a resizable array in itself is fine, just not the elements,
    // so this is NOT an error:
    ref r3: i32[*] = b.x[3];
}
