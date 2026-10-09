module Imported

import Test;

interface {
    type T (allocated);

    function MakeT(ref x: T)
        ensures x != default<T>();

    function FreeT(ref x: T)
        requires allocated(x);
        ensures !allocated(x);
}

// An (allocated) type can only be realized by a type T which satisfies
// !allocated(default<T>()). The following works, because default<i32[*]>()
// is an empty array, which counts as not-allocated.
type T = {flag: bool, arr: i32[*]};

function MakeT(ref x: T)
    ensures x != default<T>();
{
    x.flag = true;
}

function FreeT(ref x: T)
    requires allocated(x);
    ensures !allocated(x);
{
    // x is allocated if and only if x.arr is.
    // So at this point, we know allocated(x.arr),
    // and hence sizeof(x.arr) > 0.
    assert sizeof(x.arr) > 0;

    // So we can read and write x.arr[0].
    var v: i32 = x.arr[0];
    x.arr[0] = 42;

    // We can also free x.arr.
    free_array(x.arr);
}
