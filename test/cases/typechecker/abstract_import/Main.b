module Main

interface {}

import Foo;

function test1(x: Foo)
{
    fun1(x);  // Should pass
}

function test2(x: i32)
{
    fun1(x);  // Should fail, because the fact that Foo = i32 is hidden.
}
