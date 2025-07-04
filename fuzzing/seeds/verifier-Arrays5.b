module Arrays5

interface {}

import Test;

function f1(ref a: i32[,])
    requires sizeof(a).0 >= u64(10);
    requires sizeof(a).1 >= u64(8);
{
    a[0,0] = 1000;
    a[9,7] = 2000;
}

function f2(ref a: i32[10,20])
{
    a[0,0] = 1000;
    a[9,7] = 2000;
}

function test1()
{
    var a: i32[20,20];
    a[3,3] = 3333;

    f1(a);

    assert a[0,0] == 1000;
    assert a[9,7] == 2000;
    assert a[3,3] == 3333;
    assert a[1,1] == 0;

    assert a[3,3] == 0;   // negative test
}

function test2()
{
    var a: i32[*,*];
    alloc_2d_array<i32>(a, 10, 8);

    a[3,3] = 3333;

    f1(a);

    assert a[0,0] == 1000;
    assert a[9,7] == 2000;
    assert a[3,3] == 3333;
    assert a[1,1] == 0;

    assert a[3,3] == 0;   // negative test

    free_2d_array<i32>(a);
}

function test3()
{
    var a: i32[*,*];
    alloc_2d_array<i32>(a, 10, 20);

    a[3,3] = 3333;

    f2(a);

    assert a[0,0] == 1000;
    assert a[9,7] == 2000;
    assert a[3,3] == 3333;
    assert a[1,1] == 0;

    assert a[3,3] == 0;   // negative test

    free_2d_array<i32>(a);
}


// Array equality

ghost function eq_check(a: i32[], b: i32[10]): bool
{
    return a == b;
}

function test4()
{
    var a: i32[10];
    a[0] = 100;

    var b: i32[10];
    b[0] = 100;

    assert eq_check(a, b);

    b[0] = 99;
    assert eq_check(a, b);  // fails
}


// Array size matching

function test_wrong_size()
{
    var a: i32[*,*];
    alloc_2d_array<i32>(a, 5, 5);
    f2(a);  // error, size doesn't match
    free_2d_array<i32>(a);
}
