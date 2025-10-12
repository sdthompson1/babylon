module Main

interface {}

import Test;

function f1()
{
    var x: i32;
    var y: i8;
    swap x, y;   // error, different types
}

function f2()
{
    swap 1, 2;   // error, not lvalue
}

const c: i32 = 1000;

function f3()
{
    var x: i32;
    swap x, c;   // error, c is readonly
}

function f4()
{
    ghost var x: i32;
    var y: i32;
    swap x, y;        // error, x is ghost, it can't be used in executable code
    ghost swap x, y;  // error, y is nonghost, it can't be changed in a ghost statement
}
