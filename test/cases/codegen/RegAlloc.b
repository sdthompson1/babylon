module RegAlloc

// Trying to stress test register allocation somewhat.

interface { function main(); }
import Test;

function simple_loop(): i32
{
    var a0: i32;    var a1: i32;    var a2: i32;    var a3: i32;
    var b0: i32;    var b1: i32;    var b2: i32;    var b3: i32;
    var c0: i32;    var c1: i32;    var c2: i32;    var c3: i32;
    var d0: i32;    var d1: i32;    var d2: i32;    var d3: i32;

    d0 = 25;

    while (d0 > 0)
        invariant 0 <= d0 <= 100;
        decreases d0;
    {
        a3 = 99;
        d0 = d0 - 1;
    }

    return a3;
}


function complex_loop(): i32
{
    var a0: i32;    var a1: i32;    var a2: i32;    var a3: i32;
    var b0: i32;    var b1: i32;    var b2: i32;    var b3: i32;
    var c0: i32;    var c1: i32;    var c2: i32;    var c3: i32;
    var d0: i32;    var d1: i32;    var d2: i32;    var d3: i32;

    a0 = 100;
    d0 = 25;

    while (d0 > 0)
        invariant 0 <= d0 <= 100;
        decreases d0;
    {
        b0 = 1;
        b1 = 1+2;
        b2 = 1;
        b3 = (1+3*4)-1;
        c0 = 1;
        c1 = 1;
        c2 = 1;
        c3 = 1;

        if ((d0 & 1) == 0) {
            a1 = 100;
            a2 = 35;
            a3 = 99;
        } else {
            a0 = 128;
            d1 = 92;
            d2 = 1;
            d3 = 2;
        }

        d0 = d0 - 1;
    }

    return a3;
}


function swapping(x:i32): i32
{
    var a0: i32;    var a1: i32;    var a2: i32;    var a3: i32;
    var b0: i32;    var b1: i32;    var b2: i32;    var b3: i32;
    var c0: i32;    var c1: i32;    var c2: i32;    var c3: i32;
    var d0: i32;    var d1: i32;    var d2: i32;    var d3: i32;

    if (x == 0) {
        a0 = 1;
        a1 = 2;
    } else {
        a1 = 1;
        a0 = 2;
    }

    return a1;
}


function swap_mem(x:i32): i32
{
    var a0: i32;    var a1: i32;    var a2: i32;    var a3: i32;
    var b0: i32;    var b1: i32;    var b2: i32;    var b3: i32;
    var c0: i32;    var c1: i32;    var c2: i32;    var c3: i32;
    var d0: i32;    var d1: i32;    var d2: i32;    var d3: i32;

    if (x == 0) {
        a0 = 1;
        a1 = 2;
        a2=0;  a3=0;  b0=0;  b1=0;  b2=0;  b3=0;  c0=0;  c1=0;  c2=0;  c3=0;  d0=0;  d1=0;  d2=0;  d3=0;
    } else {
        a1 = 1;
        a0 = 2;
        a2=0;  a3=0;  b0=0;  b1=0;  b2=0;  b3=0;  c0=0;  c1=0;  c2=0;  c3=0;  d0=0;  d1=0;  d2=0;  d3=0;
    }

    return a1;
}

function swap_mem_2(): i32
{
    var v0  = 0;    var v1  = 1;    var v2  = 2;    var v3  = 3;
    var v4  = 4;    var v5  = 5;    var v6  = 6;    var v7  = 7;
    var v8  = 8;    var v9  = 9;    var v10 = 10;   var v11 = 11;
    var v12 = 12;   var v13 = 13;   var v14 = 14;   var v15 = 15;

    if false {
        v15 = 222;     v14 = 111;      v13 = 0;      v12 = 0;      v11 = 0;
        v10 = 0;       v9 = 0;         v8 = 0;       v7 = 0;       v6 = 0;
        v5 = 0;        v4 = 0;         v3 = 0;       v2 = 0;       v1 = 0;
        v0 = 99;
    } else {
        v14 = 111;     v15 = 222;      v13 = 0;      v12 = 0;      v11 = 0;
        v10 = 0;       v9 = 0;         v8 = 0;       v7 = 0;       v6 = 0;
        v5 = 0;        v4 = 0;         v3 = 0;       v2 = 0;       v1 = 0;
        v0 = 99;
    }

    return v15;
}


function main()
{
    Test.print_i32( simple_loop() );
    Test.print_i32( complex_loop() );
    Test.print_i32( swapping(0) );
    Test.print_i32( swap_mem(1) );
    Test.print_i32( swap_mem_2() );
}
