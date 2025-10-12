module Main

interface {}

import Test;

function f1()
{
    var x = 1;
    var y = 2;
    swap x, y;
    assert x == 2;
    assert y == 1;
    assert x == 1;  // Negative test
}

function f2()
{
    var a = {1,2,3};
    var b = {4,5,6};
    swap a, b;
    assert a == {4,5,6};
    assert b == {1,2,3};
    assert a == {1,2,3};  // Negative test
}

function f3()
{
    var a = {1,2,3};
    var b = {4,5,6};
    swap a.1, b.2;
    assert a == {1,6,3};
    assert b == {4,5,2};

    ref a0 = a.0;
    ref b1 = b.1;
    swap a0, b1;
    assert a == {5,6,3};
    assert b == {4,1,2};

    assert a == {1,2,3};  // Negative test
}

function f4()
{
    var a: i32[*];
    alloc_array<i32>(a, 10);
    
    a[1] = 2;
    a[3] = 3;

    swap a[1], a[3];

    assert a[1] == 3;
    assert a[3] == 2;

    free_array<i32>(a);
}

function f5()
{
    var a: i32[*];
    var b: i32[*];
    swap a[1/0], b[1/0];    // Error
    assert a[0] == 1;       // Error
}

function f6(): i32
{
    var a: i32[*];
    var b: i32[*];
    swap a[1/0], b[1/0];    // Error
    return 100;
}
