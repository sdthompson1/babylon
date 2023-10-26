module Postcond

interface {}

// A regression test

function f_with_postcond(): bool
    ensures 1 + 1 == 2;
{
    return true;
}

function test1(i: i32)
    requires i != 0 && f_with_postcond() == true;
{
    assert i != 0;   // Should pass.
    assert i == 0;   // Negative test -- should fail.
}


function identity(x: i32): i32
    ensures return == x;
{
    return x;
}

function test2()
{
    assert (let y = 10 in identity(y) == 10);
    assert (exists (y:i32) identity(y) == y);
}

function test3()
{
    var x: {i32,i32} = {0, 1};
    var y = identity(x.0);
    assert y == 0;
}
