module Main

interface {
    function main();
}

import MyFolder.MyModule;
import Test;

function main()
{
    Test.print_i32(imported_function());
}
