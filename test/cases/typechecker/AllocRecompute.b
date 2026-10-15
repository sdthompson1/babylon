module AllocRecompute

interface {
    // T is declared allocated, so (from the interface's point of view)
    // D is also allocated.
    type T (allocated);
    datatype D = MkD(T);

    type U;

    function main();
}

import Test;

// T is not really allocated...
type T = i32;

// ...so, inside this module, D is not allocated either, and U can be
// realized by D, even though U was declared as a normal (non-allocated) type.
type U = D;

function main()
{
    var u: U = MkD(42);
    match u {
    case MkD(x) => Test.print_i32(x);
    }
}
