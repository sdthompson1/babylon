module TypedefAbstractNotRecursive

interface {
    type T;
    datatype Foo = Mk(T);
    datatype Bar = MkBar(i32);

    function main();
}

import Test;

// OK: T is realized by a datatype from the interface, but there is no
// cycle, because Bar does not mention T
type T = Bar;

function main()
{
    var f: Foo = Mk(MkBar(42));
    match f {
    case Mk(MkBar(x)) => Test.print_i32(x);
    }
}
