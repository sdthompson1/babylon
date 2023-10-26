module Typedef
interface { function main(); }

import Test;

type Int = i32;

function f(x: Int): Int
    requires 0 < x < 10;
{
    return x + 1;
}

function main()
{
    Test.print_i32( f(9) );
}
