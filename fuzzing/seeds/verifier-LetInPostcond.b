module Main

interface {}

extern function f(x: {a:i32,b:i32}): {a:i32,b:i32}
    ensures return == { { x with a=10 } with a=20 };

function test()
{
    var v = f({a=0,b=0});
    assert v.a == 20; // ok
    assert v.a == 0;  // error
}
