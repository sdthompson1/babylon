module Imported

import Test;

interface {
    type T (allocated_always);

    datatype MaybeT = Nothing | Just(T);

    function MakeT(ref m: MaybeT);
        ensures m != Nothing;

    function FreeT(ref m: MaybeT);
        ensures m == Nothing;

    function Bad(x: T)
        requires allocated(x);
}

// An (allocated_always) type can be realized by any type whatsoever;
// here, we choose to realize it by i32.
type T = i32;

function MakeT(ref m: MaybeT)
    ensures m != Nothing;
{
    m = Just(42);
}

function FreeT(ref m: MaybeT)
    ensures m == Nothing;
{
    m = Nothing;
}

function Bad(x: T)
    requires allocated(x);
{
    // This function's precondition is always false (T is i32, and
    // allocated(x) is always false for x of type i32). Therefore, the
    // code below verifies successfully (the array-index-in-bounds
    // condition is vacuously true) but would crash if executed.
    // However, no unsoundness results, because no caller could ever
    // call this function (the precondition would never be satisfied).
    var a: i32[*];
    a[0] = 0;
}
