module Main

// Regression test for previously unsound behaviour of "type T
// (allocated);" (now fixed).

interface {
    function main();
}

import Imported;
import Test;

function main()
{
    // If T is declared as "type T (allocated);", this means that
    // T's default value is considered non-allocated, but any other
    // T-values might or might not be allocated.

    // If instead we considered the other T-values to be definitely
    // allocated, then this would be unsound, as the following test
    // demonstrates.

    var x: T;
    MakeT(x);

    // At this point, x = {flag = true, arr = []}, although the
    // current function cannot see that. It can only see that
    // x != default<T>() (guaranteed by MakeT's postcondition.)
    
    assert x != default<T>();

    // If x != default<T>() ==> allocated(x), then the call to FreeT
    // below would be allowed, and it would crash (because it would try
    // to access x.arr[0], which is out of bounds of the array).
    
    // This is why that rule would be unsound.
    
    // Instead the actual rule is that x != default<T> implies nothing
    // at all about whether allocated(x) is true, and hence, the following
    // call is a verifier error (can't prove FreeT's precondition).

    FreeT(x);
}
