module Main

interface {}

import Foo;

function foo(x: Foo): i32
{
    match x {
    case Foo1 => return 10;
    case Foo2 => return 20;
    }
}
