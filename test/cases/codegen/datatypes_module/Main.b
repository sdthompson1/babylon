module Main
interface { function main(); }

import A;

import Test;

function f1(): i32
{
    var v: A.MyType;
    match (v) {
    case A.Ctor1 => return 1;
    case A.Ctor2 => return 2;
    }
}

function main()
{
    Test.print_i32(f1());
}
