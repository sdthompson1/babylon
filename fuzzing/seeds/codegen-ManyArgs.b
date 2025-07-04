module ManyArgs
interface { function main(); }

import Test;

function f(a: i32, b: i32, c: i32, d: i32,
           e: i32, f: i32, g: i32, h: i32,
           i: i32, j: i32, k: i32, l: i32,
           m: i32, n: i32, o: i32, p: i32): i32
{
    return a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p;
}

function id(i: i32): i32
{
    return i;
}

function main()
{
    Test.print_i32( f(0, id(1), 2, id(4), 8, 16, 32, 64,
                      128, 256, 512, 1024, 2048, 4096, 8192, 16384) );
}
