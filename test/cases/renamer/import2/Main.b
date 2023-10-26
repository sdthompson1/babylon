module Main
interface {

    function main();

}

import B;

import Test;

function main()
{
    Test.print_i32(B.x + 5);
}


