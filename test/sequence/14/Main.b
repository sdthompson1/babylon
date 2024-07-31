module Main

interface {}

import Foo;

function test()
{
    match foo {
    case FooCtor(x) =>
        // This now fails, because x was changed from i8 to i16 (compared to
        // the previous test)
        assert x <= 127;
    }
}
