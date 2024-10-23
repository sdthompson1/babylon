module Arrays4

interface {}

import Test;

// Fixed sized arrays.

function f1()
{
    var a: i32[10];
    assert sizeof(a) == u64(10);
    assert forall (i: u64) i < sizeof(a) ==> a[i] == 0;

    a[3] = 6;
    assert a[3] + 1 == 7;
}

function f2()
{
    var a: i32[5,7];
    assert sizeof(a) == {u64(5), u64(7)};
    assert forall (i: u64) forall (j: u64) i < u64(5) && j < u64(7) ==> a[i,j] == 0;

    a[3,4] = 6;
    assert a[3,4] + 1 == 7;

    a[4,3] = 10;
    swap a[4,3], a[3,4];
    assert a[4,3] == 6;
    assert a[3,4] == 10;
}

const DIM: u64 = 10;

function f3()
{
    // Non-literal sizes
    var a: bool[DIM];
    var b: bool[DIM + u64(5)];
    var c: u8[sizeof(b) + u64(1)];

    var d: u32[3,4];
    var e: u32[sizeof(d).0 + u64(10)];

    assert sizeof(a) == u64(10);
    assert sizeof(b) == u64(15);
    assert sizeof(c) == u64(16);
    assert sizeof(d).0 == u64(3);
    assert sizeof(d).1 == u64(4);
    assert sizeof(e) == u64(13);

    assert !a[0];
    assert a[1];  // Should fail
}

// Array parameter (element type has validity condition)
function f4(a: u8[20])
{
    assert sizeof(a) == u64(20);
    assert forall (i: u64) i < u64(20) ==> 0 <= a[i] <= 255;
}

// Array parameter (element type doesn't have validity condition)
function f5(a: bool[20])
{
    assert sizeof(a) == u64(20);
    assert forall (i: u64) i < u64(20) ==> a[i] == true || a[i] == false;
}
