module NestedCall

// "Nested" function calls (i.e. argument to a function call is another function call)

interface { function main(); }
import Test;

function foo(x: i32): i32
{
    return ~x;
}

function main()
{
    Test.print_i32( foo(foo(foo(foo(100)))) );
}
