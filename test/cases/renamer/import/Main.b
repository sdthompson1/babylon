module Main
interface {

    function main();

}
import Import;
import OtherImport as M;

import Test;

function main()
{
    Test.print_i32( Import.x + 25 );
    Test.print_i32( M.x + 25 );
}

