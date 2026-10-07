module GhostExtern

interface {
    function main();
    ghost extern function in_interface(x: int);
}

import Test;

// Ghost extern functions are never linked, so no C implementation is needed.
ghost extern function axiom(x: int)
    ensures x * x >= int(0);

function main()
{
    ghost axiom(int(7));
    ghost in_interface(int(1));
    print_i32(42);
}
