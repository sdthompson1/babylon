module Main

interface {}

import Foo;

function foo(x: Foo): i32
{
    // This is identical to the previous test. It should fail because
    // the data ctor Foo3 was added (in module Foo), making the match
    // non-exhaustive.
    match x {
    case Foo1 => return 10;
    case Foo2 => return 20;
    }
}
