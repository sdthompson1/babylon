module Main

interface {
    function main();
}

import Foo;
import Test;

function test(x: Foo)
{
    // This should typecheck successfully
    fun1(x);
}

function main()
{
    print_string("Done\n");
}
