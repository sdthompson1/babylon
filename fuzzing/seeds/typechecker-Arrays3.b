module Main

interface {}

function f_resizable(a: i32[*], b: i32[*,*])
{
    var s1: u64       = sizeof(a);   // ok
    var s2: {u64,u64} = sizeof(a);   // type error
    var s3: u64       = sizeof(b);   // type error
    var s4: {u64,u64} = sizeof(b);   // ok

    var i1: i32  = a[0];    // ok
    var i2: bool = a[1];    // type error
    var i3: i32  = a[0,0];  // wrong number of indices

    var i4: i32  = b[0,0];  // ok
    var i5: bool = b[0,0];  // type error
    var i6: i32  = b[0];    // wrong number of indices
}

function f_incomplete(a: i32[], b: i32[,])
{
    var s1: u64       = sizeof(a);   // ok
    var s2: {u64,u64} = sizeof(a);   // type error
    var s3: u64       = sizeof(b);   // type error
    var s4: {u64,u64} = sizeof(b);   // ok

    var i1: i32  = a[0];    // ok
    var i2: bool = a[1];    // type error
    var i3: i32  = a[0,0];  // wrong number of indices

    var i4: i32  = b[0,0];  // ok
    var i5: bool = b[0,0];  // type error
    var i6: i32  = b[0];    // wrong number of indices
}

function f_sized(a: i32[10], b: i32[10,20])
{
    var s1: u64       = sizeof(a);   // ok
    var s2: {u64,u64} = sizeof(a);   // type error
    var s3: u64       = sizeof(b);   // type error
    var s4: {u64,u64} = sizeof(b);   // ok

    var i1: i32  = a[0];    // ok
    var i2: bool = a[1];    // type error
    var i3: i32  = a[0,0];  // wrong number of indices

    var i4: i32  = b[0,0];  // ok
    var i5: bool = b[0,0];  // type error
    var i6: i32  = b[0];    // wrong number of indices
}

function test(i1: i32[], i2: i32[,])
{
    var r1: i32[*];
    var r2: i32[*,*];

    var s1: i32[10];
    var s2: i32[10,20];

    f_resizable(r1, r2);   // ok
    f_resizable(i1, i2);   // error, cannot cast to resizable
    f_resizable(s1, s2);   // error, cannot cast to resizable

    f_incomplete(r1, r2);  // ok
    f_incomplete(i1, i2);  // ok
    f_incomplete(s1, s2);  // ok

    f_sized(r1, r2);   // ok, but proof required
    f_sized(i1, i2);   // ok, but proof required
    f_sized(s1, s2);   // ok

    var w1: i32[1];
    var w2: i32[1,1];
    f_sized(w1, w2);   // error, wrong size
}

function test2()
{
    var x: i8[];   // error
    var y: i8[*];  // ok
    var z: i8[10]; // ok
}

function test3(): i8[]    // this is not allowed
{}

function test4(): i8[*]   // ok
{
    var r: i8[*];
    return r;        // ok
}

function test5(): i8[10]   // ok
{
    var s: i8[10];
    return s;        // ok
}

function test6(r: i8[*], s: i8[10], i: i8[]): i8[10]
{
    if true {
        return r;   // ok
    } else if true {
        return s;   // ok
    } else {
        return i;   // ok
    }
}

function test7(ref i1: i8[], ref i2: i8[])
{
    var r1: i8[*];
    var r2: i8[*];
    var s1: i8[10];
    var s2: i8[10];

    r1 = r2;    // ok
    s1 = s2;    // ok
    i1 = i2;    // error, assign of incomplete types not implemented yet

    var x = (let tmp = i1 in tmp[0]);  // ok (copies descriptor)
    var y = (let tmp = r1 in tmp[0]);  // ok (copies descriptor)
    var z = (let tmp = s1 in tmp[0]);  // ok (but inefficient, copies whole array)

    swap r1, r2;   // ok
    swap s1, s2;   // ok
    swap i1, i2;   // error, swap of incomplete types not implemented yet
}

function test8(x: i32[], y: i32[10], z: i32[*])
    requires sizeof(x) == u64(10);
    requires sizeof(z) == u64(10);
{
    var b: bool = (x == y);       // error, can't compare arrays
    ghost var g: bool = (x == y); // but you can compare arrays in ghost code
    ghost var g2: bool = (x == y != z);   // chaining also works    
}

ghost function test9(x: i32[], y: i32)
{
    var b: bool = x == y;   // error
}

ghost function test10(x: i32[])
{
    var b: bool = allocated(x);  // Error, can't determine if T[] is allocated or not.
}

function incomplete_array_tuple(x: i32[], y: i32[]): {i32[], i32[]}
{
    return {x, y};  // error: returning an incomplete type not allowed (yet?)
}

datatype Foo = Foo(i32[]);

function incomplete_datatype(a: i32[])
{
    var x: Foo;     // error: putting incomplete array type into a variable
    var y = Foo(a); // error: putting incomplete array type into a variable
    ghost var gx: Foo;      // ok, ghost code
    ghost var gy = Foo(a);  // ok, ghost code
}

function array_of_incomplete_arrays(ref x: (i32[])[10], ref y: (i32[])[10])
{
    x = y;   // error: assigning incomplete arrays not allowed
    swap x[0], y[0];   // error: nor is swapping
    
    ghost var v: (i32[])[10] = x;  // ok, ghost code
    ghost var w = y;  // ok
    ghost swap v, w;  // ok
}
