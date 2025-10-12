module Main

// Fixed-sized arrays

interface {
    function main();
}

import Test;

function fixed_array_1d()
{
    var a: i32[10];
    a[2] = 4;
    a[6] = 9;

    print_i32(a[2] + a[6] + a[7]); // prints 13 (a[7] defaults to 0)

    print_u64(sizeof(a));   // prints 10

    var r = {u64(0)};
    r.0 = sizeof(a);   // force sizeof result to be stored to memory
    print_u64(r.0);    // prints 10
}

function fixed_array_2d()
{
    var a: u8[8,7];

    a[2,3] = 100;
    a[3,5] = 90;
    print_u8(a[2,3] + a[3,5]);  // prints 190

    print_u64(sizeof(a).0);  // prints 8
    print_u64(sizeof(a).1);  // prints 7

    var s = sizeof(a);
    print_u64(s.0);  // prints 8
    print_u64(s.1);  // prints 7
}

function fixed_array_1d_ref()
{
    var a: i16[10];
    ref elt = a[5];
    elt = 200;
    print_i16(a[5]);   // prints 200
}

function fixed_array_3d_ref()
{
    var a: i32[5,3,7];
    ref elt = a[1,2,3];
    elt = 250;
    print_i32(a[1,2,3]);  // prints 250
}

function f(a: i32[2,3])
{
    print_i32(a[1,2]);
}

function pass_array_param()
{
    var a: i32[2,3];
    a[1,2] = 99;
    f(a);  // prints 99
}

function zero_size_array()
{
    var a: i32[0];
}

function main()
{
    fixed_array_1d();
    fixed_array_2d();
    fixed_array_1d_ref();
    fixed_array_3d_ref();
    pass_array_param();
    zero_size_array();
}
