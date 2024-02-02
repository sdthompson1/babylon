module Ref

// Tests of references, and "assign to tuple field".

interface { function main(); }
import Test;

// Assign to ref to local var
function f1(): i16
{
    var x: i16 = 1234;
    ref r: i16 = x;
    r = 2345;
    return x;
}


// Assign to ref to a tuple field
function f2(): i32
{
    var v = {{1,2,3},4,5};

    ref r = v.0.1;
    r = 1000;

    match (v) {
    case {{_,x,_},_,_} => return x;
    }
}


// Assign directly to a tuple field (using "a.b" syntax on lhs)
function f3(): i32
{
    var v = {{1,2,3},4,5};

    v.0.1 = 999;

    match (v) {
    case {{_,x,_},_,_} => return x;
    }
}


// Assign to the entire tuple (using ref)
function f4(): i32
{
    var v = {{1,2,3},4,5};

    ref r = v.0;
    r = {10,11,12};

    return v.0.1;
}


// Assign to the entire tuple (using "a.b" syntax)
function f5(): i32
{
    var v = {{1,2,3},4,5};

    v.0 = {20,21,22};

    return v.0.1;
}


// Assign to ref obtained through match
function f6(): i32
{
    var x = {{1,2,3},4,5};
    match (x.0) {
    case {_,_,ref y} => y = 1832;
    }
    assert (x == {{1,2,1832},4,5});
    return x.0.2;
}


// Read from ref
function f8(): i32
{
    var x = 1;
    ref r = x;
    r = r + 1;
    return r + 1;
}


// Complex refs
function f9(): i32
{
    var a: i32[10];
    
    ref r = a[{1,2,3}.1];
    r = 1000;
    var result = a[2];
    
    return result;
}

function f10(): i32
{
    var a: {i32[6],i32}[10][5];

    ref r = a[2-1][1+1].0[3];
    r = 100;
    var result = a[1][2].0[3];

    return result;
}

function main()
{
    Test.print_i16( f1() );
    Test.print_i32( f2() );
    Test.print_i32( f3() );
    Test.print_i32( f4() );
    Test.print_i32( f5() );
    Test.print_i32( f6() );
    Test.print_i32( f8() );
    Test.print_i32( f9() );
    Test.print_i32( f10() );
}
