module Main

interface {}

import Import;

function test1()
{
    assert i32(f1()) < 1000;
}

function test2()
{
    var x: i8;
    f2(x);
    assert i32(x) < 1000;
}

function test3()
{
    var x: i8;
    var y: i8;
    var z: i8 = f3(x, y);
    assert i32(x) < 1000;
    assert i32(y) < 1000;
    assert i32(z) < 1000;

    // Negative test
    // (this should fail because the implementation of f3 is hidden.)
    assert z == 10;
}
