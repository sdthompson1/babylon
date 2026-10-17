module GhostRecomputeNested

interface {
    // T is ghost, so (from the interface's point of view) E is a ghost
    // datatype, and therefore so is D.
    ghost type T;
    datatype E = MkE(T);
    datatype D = MkD(E);

    function main();
}

import Test;

// T is realized by a runtime type...
type T = i32;

// ...so, inside this module, E is no longer ghost, and therefore neither
// is D, which can be used in executable code.
function f(): i32
{
    var d: D = MkD(MkE(42));
    match d {
    case MkD(MkE(x)) => return x;
    }
}

function main()
{
    Test.print_i32(f());
}
