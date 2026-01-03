module GhostArg
interface { function main(); }
import Test;

function add(x: i32, ghost debug: bool, y: i32): i32
    requires -100 < x < 100;
    requires -100 < y < 100;
{
    // debug argument exists for verification but not in generated code
    return x + y;
}

function with_ref(ref x: i32, ghost ref g: i32)
    requires 0 < x < 1000;
    requires 0 < g < 1000;
{
    x = x + 1;
    ghost g = g + 100;  // only affects verification
}

function main()
{
    var result = add(5, true, 10);
    Test.print_i32(result);  // Should print 15

    var x = 100;
    ghost var g = 1;
    with_ref(x, g);
    Test.print_i32(x);  // Should print 101
}
