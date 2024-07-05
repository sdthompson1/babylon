module Main

interface {}

import AbsType;

function test()
{
    var foo: Foo;
    var foo2: Foo;
    reset_foo(foo2);
    assert foo == foo2;  // succeeds

    foo = new_foo();
    set_foo_value(foo, 10);
    assert get_foo_value(foo) == 10;  // succeeds

    assert get_foo_value(foo) == 11;  // fails
}


