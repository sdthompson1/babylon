module Main

interface {
    function main();
}

import A;   // imports from dep1
import B;   // imports from dep2

function main()
{
    A.func();
    B.func();
}
