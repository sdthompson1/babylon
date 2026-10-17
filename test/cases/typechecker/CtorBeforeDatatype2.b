module CtorBeforeDatatype2

interface {
    function main();
}

import Test;

// OK: the array dimension N of A uses the data constructor MkD, without
// naming the datatype D itself. So D must be processed before N, which
// must be processed before A.
datatype A = MkA(i32[N]);
const N: u64 = match MkD(3) { case MkD(n) => n };
datatype D = MkD(u64);

function main()
{
    var a: A = MkA([10, 20, 30]);
    match a {
    case MkA(arr) => Test.print_i32(arr[2]);
    }
}
