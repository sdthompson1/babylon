module GhostRecomputeRealize

interface {
    // T is ghost, so (from the interface's point of view) D is a ghost
    // datatype.
    ghost type T;
    datatype D = MkD(T);

    type U;

    function main();
}

import Test;

// T is realized by a runtime type...
type T = i32;

// ...so, inside this module, D is not ghost, and U can be realized by D,
// even though U was declared as a normal (non-ghost) type.
type U = D;

function main()
{
    var u: U = MkD(42);
    match u {
    case MkD(x) => Test.print_i32(x);
    }
}
