module Main

interface {}

import Foo;

ghost function test1(): bool
{
    var d: D = make_d(1);  // Should pass, this is ghost code
    return true;
}

function test2()
{
    // Should fail. Foo's implementation knows that T = i32, but this
    // module can only see Foo's interface, which says that T (and hence D)
    // is ghost.
    var d: D;
}
