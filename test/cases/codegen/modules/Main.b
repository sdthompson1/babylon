module Main
interface {
    function main();
}

import Imported;
import Test;

function main()
{
    Test.print_i32( Imported.add(1, 2) );
}

