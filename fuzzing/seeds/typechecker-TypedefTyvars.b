module Main
interface {}
import Test;

type Pair<a,b> = {a, b};

function f2(x: Pair<i32, i32>): i32
    requires x.0 < 100;
    requires x.1 < 100;
{
    return x.0 + x.1;
}

function f3()
{
    var x: Pair<i32, i32, i32> = 100;       // Error
    var y: Pair<i32, i32> = {1, 2};         // OK
    var z: i32 = f2(y);                     // OK
}

type Bad = Pair<i32>;     // Invalid rhs - kind-check fails
