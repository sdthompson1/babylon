module Main

// Codegen for statements (e.g. ifs)

interface { function main(); }
import Test;


function simple_if(x: i32): i32
{
    if x == 1 {
        return 25;
    } else {
        return 50;
    }
}


function complex_if(x: i32, y: i32): i16
{
    var z: u8 = 99;
    if (x == 1) {
        if (y == 1) {
            return 200;
        } else {
            z = z - 1;
        }
    } else {
        if (x == 2) {
            z = 88;
        } else {
            z = 99;
        }
        z = z - 10;
    }
    z = z - 10;
    return z;
}


const global_bool: bool = true;

function if_global_bool(): i8
{
    if (global_bool) {
        return 99;
    } else {
        return 100;
    }
}


function while_loop(): i32
{
    var i: i32 = 0;
    var sum: i32 = 0;
    
    while (i < 10)
        invariant 0 <= i <= 10;
        invariant sum == i * (i + 1) / 2;
        decreases 10 - i;
    {
        i = i + 1;
        sum = sum + i;
    }

    assert (sum == 55);

    return sum;
}


function while_loop_2(): i32
{
    var x = {5, 5};

    while x.0 > 0
        invariant 0 <= x.0 <= 5;
        invariant x.1 == 10 - x.0;
        decreases x.0;
    {
        x.0 = x.0 - 1;
        x.1 = x.1 + 1;
    }

    return x.1;
}


function f()
{
}

// This is to check that calling a function such as f() does not crash the
// generated code.
// Functions don't yet have any side-effects, so we are not able to test 
// whether f "does anything", currently. All we can do is call it.
function call_stmt_in_loop(): i32
{
    var x: i32 = 10;
    while (x > 0)
        decreases x;
    {
        f();
        x = x - 1;

        // some ghost stmts in while-loop (should not affect codegen)
        ghost var a:i32 = 0;
        obtain (b:i32) b!=a;

    }
    return 987;
}


function default_int(): i32
{
    var v: i32;
    return v;
}

function default_bool(): bool
{
    var b: bool;
    return b;
}


function return_with_no_value()
{
    if (true) {
        Test.print_i32(999);
        return;
    }
    Test.print_i32(998);  // not printed
}

function main()
{
    Test.print_i32( simple_if(1) );
    Test.print_i32( simple_if(2) );

    Test.print_i16( complex_if(1, 1) );
    Test.print_i16( complex_if(1, 2) );
    Test.print_i16( complex_if(2, 0) );
    Test.print_i16( complex_if(3, 0) );

    Test.print_i8( if_global_bool() );

    Test.print_i32( while_loop() );
    Test.print_i32( while_loop_2() );

    Test.print_i32( call_stmt_in_loop() );

    Test.print_i32( default_int() );
    Test.print_bool( default_bool() );

    return_with_no_value();
}
