module ResizableRefs

interface {}

import Test;

// References to elements of resizable arrays. Each time such a
// reference is used, the verifier must check that the element still
// exists (i.e. the index is still within the bounds of the array).

datatype Maybe = Nothing | Just(i32);

function f1()
{
    var a: i32[*];
    alloc_array(a, 10);

    ref r = a[9];
    r = 1;
    assert a[9] == 1;

    // Replace the array with a larger one; the ref is still valid,
    // and refers to element 9 of the new array
    free_array(a);
    alloc_array(a, 20);
    assert r == 0;
    r = 2;
    assert a[9] == 2;

    // Replace the array with a smaller one; the ref is now invalid
    free_array(a);
    alloc_array(a, 9);
    var v = r;      // Error, reading invalid ref
    r = 3;          // Error, writing invalid ref

    free_array(a);
}

function f2()
{
    var a: i32[*];
    alloc_array(a, 10);
    ref r = a[9];

    var b: i32[*];
    alloc_array(b, 5);
    swap a, b;

    ref r2 = r;     // Error, a[9] no longer exists

    free_array(a);
    free_array(b);
}

function resize(ref a: i32[*])
    requires sizeof(a) > u64(0);
    ensures sizeof(a) > u64(0);
{
    free_array(a);
    alloc_array(a, 1);
}

function f3()
{
    var a: i32[*];
    alloc_array(a, 10);

    ref r0 = a[0];
    ref r1 = a[1];

    resize(a);

    r0 = 1;         // OK, a is known to have at least one element
    r1 = 1;         // Error, a might have only one element

    free_array(a);
}

function f4()
{
    var a: Maybe[*];
    alloc_array(a, 2);
    a[1] = Just(1);

    match a[1] {
    case Just(ref x) =>
        x = 2;
        assert a[1] == Just(2);

        free_array(a);
        alloc_array(a, 1);
        x = 3;      // Error, a[1] no longer exists

    case Nothing =>
    }

    free_array(a);
}

function f5()
{
    var a: i32[*,*];
    alloc_2d_array(a, 3, 4);

    ref r = a[2,3];

    free_2d_array(a);
    alloc_2d_array(a, 4, 4);
    r = 1;          // OK
    assert a[2,3] == 1;

    free_2d_array(a);
    alloc_2d_array(a, 4, 3);
    r = 2;          // Error, second index now out of range

    free_2d_array(a);
}

function f6()
{
    var a: {x: i32, y: i32[*]}[*];
    alloc_array(a, 2);
    alloc_array(a[1].y, 5);

    ref r = a[1].y[4];
    r = 1;
    assert a[1].y[4] == 1;

    free_array(a[1].y);
    r = 2;          // Error, inner array is now empty

    free_array(a);
}
