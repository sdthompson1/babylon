module Main
interface {}

function f1(ref x: i32, y: ref i32, z: i32)
{
    x = 99;
}

function f2()
{
    var x: i32;
    var y: i32;

    f1(x, y, 100);     // OK
    f1(x, 100, y);     // Error, can't reference 100
}

function f3(ref x: i32): i32
{
}

function f4()
{
    var x1: i32;
    var x2 = f3(x1);       // OK
    var x3 = f3(f3(x1));   // Error, can't have refs in sub-expressions
    var x4 = f3(x1) + 1;   // Error, can't have refs in sub-expressions
}

function f5(x: i32, ref y: i32)
{
}

function f6()
{
    var x: i32;
    f5(100, x);     // OK
}

function f7(ref x: i32)
    ensures match (x) { case ref xx => true };    // Error, match ref in postcondition
{
}


const const_test: i32 = 100;

function f8(x: i32)
{
    var x1 = f3(x);            // error, "x" is const, can't pass by reference
    var x2 = f3(const_test);   // error, "const_test" is const
}


function id(x: i32): i32
{
    return x;
}

function f9(b: bool): i32
{
    var x: i32;
    if b {
        return f3(x);  // Allowed
    } else {
        return id(f3(x));  // Not allowed
    }
}
