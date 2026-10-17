module CtorBeforeDatatype

interface {
    function main();
}

import Test;

// OK: main uses the data constructor MkD before the datatype D is
// declared (and never mentions the name D itself)
function main()
{
    var x = MkD(42);
    match x {
    case MkD(n) => Test.print_i32(n);
    }
}

datatype D = MkD(i32);
