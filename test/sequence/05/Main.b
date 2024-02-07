module Main

interface {}

// Setup some datatype tests.

datatype Foo = Foo1(i32) | Foo2(bool);

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

function i(): i32
{
    var v = Foo2(true);
    return 0;
}

function bar_func(x: Bar): i32
{
    return 1 + 1;
}
