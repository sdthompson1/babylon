module GhostRecompute

interface {
    // T is ghost, so (from the interface's point of view) D is a ghost
    // datatype.
    ghost type T;
    datatype D = MkD(T);

    function main();
}

import Test;

// T is realized by a runtime type...
type T = i32;

// ...so, inside this module, D can be used in executable code.
function f(): i32
{
    var d: D = MkD(42);
    match d {
    case MkD(x) => return x;
    }
}

function main()
{
    Test.print_i32(f());
}
