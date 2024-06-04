module Arrays

import Test;

interface {}

const u64_zero: u64 = 0;
const u64_max:  u64 = 18446744073709551615;

function f5(ref a: i32[])
{
    assert (u64_zero <= sizeof(a) <= u64_max);
}

function f6(ref a: i32[,])
{
    assert (u64_zero <= sizeof(a).0 <= u64_max);
    assert (u64_zero <= sizeof(a).1 <= u64_max);
}

function f7()
{
    var a: i8[*];
    assert (sizeof(a) == u64_zero);
    var b: i8[*,*,*];
    assert (sizeof(b) == {u64_zero, u64_zero, u64_zero});
}

function f9()
{
    var a: i32[100];

    var i: u64 = 0;
    while (i < 100)
        invariant sizeof(a) == 100;
        invariant i <= 100;
        invariant forall (j:u64) j < i ==> a[j] == i32(j);
        decreases 100 - i;
    {
        a[i] = i;
        i = i + 1;
    }

    assert (forall (i:u64) i < 100 ==> a[i] == i32(i));

    ref r = a[3];
    assert (r == 3);
    r = 4;
    assert (a[3] == 4);
}

function f10()
{
    var a: i32[10,20];
    
    a[4,6] = 123;
    ref r = a[4,6];
    assert (r == 123);
    r = 456;
    assert (a[4,6] == 456);
}

function f11(ref a: i32[])
{
    a[sizeof(a)] = 0;    // Error, out of bounds
}

function f13(ref a: i32[], ref b: i32[,])
{
    a[1/0] = 1;    // Error, index failed to verify, failed to cast, might be out of bounds
    a[999] = 1;    // Error, index out of bounds

    b[1, 2/0] = 0;  // Error, index failed to verify, failed to cast, might be out of bounds
    b[1, 999] = 0;  // Error, index out of bounds
}

function f14()
{
    var a: i32[*];
    resize_array<i32>(a, 10);
    // Error: a was not deallocated
}
