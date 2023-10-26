module Main
interface {}


import A;

function test(): i32
{
    var v: i32 = A.foo();

    v = A.foo();   // OK
    v = A.bar();   // Error

    assert (A.foo() == 99);    // OK
    assert (A.bar() == 100);   // Error

    return A.foo();
}

