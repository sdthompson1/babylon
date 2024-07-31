module Main

interface {}

import Foo;

function test()
{
    match foo {
    case FooCtor(x) =>
        // This should succeed because x is i8
        assert x <= 127;
    }
}
