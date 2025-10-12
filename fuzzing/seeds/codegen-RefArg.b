module Main

// Pass-by-reference arguments

interface { function main(); }
import Test;

function f(ref x: i32)
    requires x < 1000;
{
    x = x + 1;
}

function g(): i32
{
    var v: i32 = 234;
    f(v);
    return v;
}


function f2(ref x: {u8, bool}): i32
{
    x.0 = ~x.0;
    x.1 = !x.1;
    return 99;
}

function f3(): {u8, bool, i32}
{
    var r = {u8(3), false};
    var ret = f2(r);
    return {r.0, r.1, ret};
}


function g1(ref x: i32): i32
    requires 0 <= x <= 10;
{
    x = x + 1;
    return x + 2;
}

function call_g1(ref x: i32): i32
    requires 0 <= x <= 8;
{
    x = x + 2;
    return g1(x);
}


function main()
{
    Test.print_i32  ( g() );
    Test.print_u8   ( f3().0 );
    Test.print_bool ( f3().1 );
    Test.print_i32  ( f3().2 );

    var x = 1;
    var r = call_g1(x);
    Test.print_i32(x);  // 4
    Test.print_i32(r);  // 6
}
