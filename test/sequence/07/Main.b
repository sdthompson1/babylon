module Main

interface {}

// Change the definition of the datatype. This should cause
// f, g, h and i to all be reverified.

datatype Foo = Foo1(i64) | Foo2(bool);

datatype Bar = Bar1(i32) | Bar2(bool) | Bar3(Foo);

function f(x: Foo): bool
{
    match x {
    case Foo1(_) => return true;
    case Foo2(_) => return false;
    }
}

function g(x: Foo): i32
{
    return 1 + 2;
}

function h(): Foo
{
    return Foo2(true);
}

// This tests that a function reverifies even if it doesn't mention the
// datatype name (Foo) explicitly, but only a data constructor name (Foo2).
function i(): i32
{
    var v = Foo2(true);
    return 0;
}

// This tests whether bar_func reverifies because the definition of Foo
// (which Bar depends on) changed.
function bar_func(x: Bar): i32
{
    return 1 + 1;
}
