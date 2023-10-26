module StructReturn
interface { function main(); }

import Test;

function foo(x: {i32,i32}): {i32,i32}
    requires -100 < x.0 < 100;
    requires -100 < x.1 < 100;
{
    return {x.0 + x.1, x.0 - x.1};
}

function main()
{
    var s = { 10, 20 };
    s = foo(s);
    assert (s.0 == 30);
    assert (s.1 == -10);
    Test.print_i32(s.0);
    Test.print_i32(s.1);
}

