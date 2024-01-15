module Arrays2

interface {}

function test1()
{
    ghost var b: i32[int(1)];   // error: size must be a finite int type
}

function f(a: i32[10])
{}

function test2()
{
    var a: i32[20];
    var b: bool[10];
    var c: i32[10,10];
    var d: i32[10];
    f(a);  // error: size mismatch
    f(b);  // error: element type mismatch
    f(c);  // error: number of dimensions mismatch
    f(d);  // ok
}

datatype A = A;

function test3(sz: i32)
{
    var a: A<i32>[20];     // error: kind error in element-type
    var b: i32[1, 2, 1 + true];  // error: type error in size
    var c: i32[sz];   // error: size is not a compile-time constant
}
