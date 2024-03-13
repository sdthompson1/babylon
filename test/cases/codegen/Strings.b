module Strings

interface {
    function main();
}

import Test;

function foo(str: u8[])
    requires valid_string(str);
{
    Test.print_string(str);
}

function main()
{
    ref s = "Hello world!\n";
    ref t = s;
    foo(t);
    Test.print_string("");
    foo("Test 123\n");
    Test.print_string("");
}
