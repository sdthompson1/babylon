module Methods

// Some simple function calls

interface { function main(); }
import Test;

function foo(): i32
{
    return 100;
}

function bar(): i32
{
    var x: i32 = 99;
    x = x + 2;
    return x - 3;
}

function with_args(x: i32, y: i32): i32
{
    return x & y;
}

function calls_bar(): i32
{
    var x: i32 = 10;
    var y: i32 = 4 * bar();
    return x + y;
}

function local_not_in_register(): i32
{
    var r1: i32;  var r2: i32;  var r3: i32;  var r4: i32;
    var r5: i32;  var r6: i32;  var r7: i32;  var r8: i32;
    var r9: i32;  var r10: i32;  var r11: i32;  var r12: i32;
    var r13: i32;  var r14: i32;  var r15: i32;  var r16: i32;
    var retval: i32;
    var x1: i32;   var x2: i32;   var x3: i32;   var x4: i32;
    var x5: i32;   var x6: i32;   var x7: i32;   var x8: i32;
    var x9: i32;   var x10: i32;  var x11: i32;  var x12: i32;
    var x13: i32;  var x14: i32;  var x15: i32;  var x16: i32;
    retval = 99;
    var y1: i32;   var y2: i32;   var y3: i32;   var y4: i32;
    var y5: i32;   var y6: i32;   var y7: i32;   var y8: i32;
    var y9: i32;   var y10: i32;  var y11: i32;  var y12: i32;
    var y13: i32;  var y14: i32;  var y15: i32;  var y16: i32;
    return retval;
}

function returns_bool(): bool
{
    assert (2 > 1);    // Testing that "assert" doesn't impact codegen
    return 2 > 1;
}


const test_const: i32 = 98;


function voidfn(x: i32)
{
}

function call_void_twice(): i32
{
  voidfn(1);
  voidfn(2);
  return 1923;
}


function tuple_arg(x: {i32,i32}, ref y: i32)
{
    Test.print_i32(y);
}

function g(x: {i32,i32}): i32
{
    return 10;
}

function f(ref x: i32, y: i32, ref z: i32)
{
    print_i32(x);
    print_i32(y);
    print_i32(z);
}

function main()
{
    Test.print_i32( foo() );
    Test.print_i32( bar() );
    Test.print_i32( with_args(12, 4+1) );
    Test.print_i32( calls_bar() );
    Test.print_i32( local_not_in_register() );
    Test.print_bool( returns_bool() );
    Test.print_i32( test_const );
    Test.print_i32( call_void_twice() );

    // regression test - 2 args, each requiring a temp block (of different size)
    var v = 3;
    tuple_arg({1,2},v);

    // regression test - more complex case with 2 calls
    var a = 1;
    var b = 40;
    f(a, g({1,2}), b);    
}
