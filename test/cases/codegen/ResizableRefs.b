module ResizableRefs

// References to elements of resizable arrays.

// Such a reference refers to an index position in the array (not to a
// fixed memory address), so it must remain usable even if the array's
// memory moves (so long as the index is still in range).

// To guarantee that the memory moves, we allocate a second array and
// swap it with the first. The old memory is kept alive until after the
// ref has been used, and then the contents of both the old and new
// memory are printed. (If the ref was wrongly still pointing into the
// old memory, the wrong values would be printed.)

interface {
    function main();
}

import Test;

datatype Maybe = Nothing | Just(i32);

function set(ref x: i32, v: i32)
    ensures x == v;
{
    x = v;
}

// Basic read and write, before and after the array moves.
function test1()
{
    var a: i32[*];
    alloc_array(a, 10);
    a[3] = 33;

    ref r = a[3];
    print_i32(r);
    r = 34;
    print_i32(a[3]);

    var b: i32[*];
    alloc_array(b, 20);
    b[3] = 1;
    swap a, b;

    print_i32(r);
    r = 35;
    print_i32(a[3]);
    print_i32(b[3]);
    a[3] = 36;
    print_i32(r);

    // Shrink the array; the index is still (just) in range
    var c: i32[*];
    alloc_array(c, 4);
    swap a, c;

    r = 37;
    print_i32(a[3]);
    print_i32(c[3]);

    free_array(a);
    free_array(b);
    free_array(c);
}

// The index is evaluated when the ref is created, not when it is used.
function test2()
{
    var a: i32[*];
    alloc_array(a, 10);

    var i: u64 = 2;
    ref r = a[i];
    i = 4;

    var b: i32[*];
    alloc_array(b, 10);
    swap a, b;

    r = 100;
    print_i32(a[2]);
    print_i32(a[4]);
    print_i32(b[2]);

    free_array(a);
    free_array(b);
}

// 'ref' pattern variables, when matching on an array element.
function test3()
{
    var a: Maybe[*];
    alloc_array(a, 1);
    a[0] = Just(1);

    match a[0] {
    case Just(ref x) =>
        var b: Maybe[*];
        alloc_array(b, 1);
        b[0] = Just(2);
        swap a, b;

        print_i32(x);
        x = 5;

        match b[0] {
        case Just(y) => print_i32(y);
        case Nothing => print_i32(-1);
        }

        free_array(b);

    case Nothing =>
    }

    match a[0] {
    case Just(y) => print_i32(y);
    case Nothing => print_i32(-1);
    }

    free_array(a);
}

// Nested resizable arrays, and refs made from another ref.
function test4()
{
    var a: {x: i32, y: i32[*]}[*];
    alloc_array(a, 3);
    alloc_array(a[1].y, 5);

    var i: u64 = 1;
    ref elt = a[i];
    ref r = elt.y[i + 3];
    ref s = elt.x;
    i = 0;

    r = 10;
    s = 11;
    print_i32(a[1].y[4]);
    print_i32(a[1].x);

    // Move the inner array
    var c: i32[*];
    alloc_array(c, 8);
    swap elt.y, c;

    r = 12;
    print_i32(a[1].y[4]);
    print_i32(c[4]);

    set(r, 13);
    print_i32(elt.y[4]);

    swap r, s;
    print_i32(a[1].y[4]);
    print_i32(a[1].x);

    // Move the outer array
    var d: {x: i32, y: i32[*]}[*];
    alloc_array(d, 3);
    swap a, d;

    s = 14;
    print_i32(a[1].x);
    print_i32(d[1].x);

    free_array(c);
    free_array(d[1].y);
    free_array(d);
    free_array(a);
}

// Two-dimensional arrays; the new array has different dimensions.
function test5()
{
    var a: i32[*,*];
    alloc_2d_array(a, 3, 4);

    ref r = a[2,3];
    r = 20;
    print_i32(a[2,3]);

    var b: i32[*,*];
    alloc_2d_array(b, 30, 40);
    swap a, b;

    a[3,2] = 21;
    r = 22;
    print_i32(a[2,3]);
    print_i32(a[3,2]);
    print_i32(b[2,3]);

    free_2d_array(a);
    free_2d_array(b);
}

function main()
{
    test1();
    test2();
    test3();
    test4();
    test5();
}
