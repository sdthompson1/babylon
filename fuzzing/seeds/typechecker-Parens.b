module Main

interface {}

function foo(a: (i32[,])[], b: i32[][,])
{
    var x1: i32 = a[1][2,3];  // ok
    var x2: i32 = a[2,3][1];  // error

    var x3: i32 = b[1][2,3];  // ok
    var x4: i32 = b[2,3][1];  // error

    ghost var eq: bool = (a == b);  // ok
}
