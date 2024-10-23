module Arrays3

interface{}

import Test;

ghost function f(x: i32): i32;

// Regression test for bug relating to "default" arrays
function foo(ref a: i32[])
    requires sizeof(a) == u64(2);
    requires a[0] == 1;
{
    var empty: i32[*];
    assert sizeof(empty) == u64(0);

    // This was previously succeeding, but a[1] is not equal to 1 (in general),
    // so it should fail.
    // Unfortunately it now times out, rather than failing outright, but I didn't
    // find any way to repro the bug otherwise.
    assert a[1] == 1;

    free_array(empty);
}
