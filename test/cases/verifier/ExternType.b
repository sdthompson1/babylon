module ExternType

interface {}

extern type Foo;

function f(x: Foo)
{
    var v1: Foo;
    var v2: Foo;

    assert x == x;     // Passes
    assert v1 == v2;   // Passes, v1 and v2 are both equal to "default"

    assert v1 == x;    // Fails, x could have any value
}

