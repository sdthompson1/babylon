module Main

interface {}

extern impure function foo(): i32;
extern function bar(): i32;
extern ghost function baz(): i32;  // Error: extern ghost not allowed.

ghost function f1(): i32
{
    assert foo() == foo();   // Error: can't call impure function from ghost code (x2)
    return foo();   // Error: can't call impure function from ghost code.
}

function f2(): i32
{
    return foo();   // Error: can't call impure function from pure function.
}

impure function f3(): i32
{
    return foo();   // OK.
}

impure ghost function f4()    // Error: impure ghost function not allowed.
{}
