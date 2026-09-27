module ArraySizePreserved

interface {}

import Test;

// Writing to a ref parameter of incomplete array type (T[]) must not change
// the array's size, because the caller might have passed a fixed-size array.

ghost function swap_bad(ref x: i32[], ref y: i32[])
{
    swap x, y;    // Error
}

ghost function assign_bad(ref x: i32[], y: i32[])
{
    x = y;        // Error
}

ghost function swap_ok(ref x: i32[], ref y: i32[])
    requires sizeof(x) == sizeof(y);
{
    swap x, y;
}

ghost function assign_ok(ref x: i32[], y: i32[])
    requires sizeof(x) == sizeof(y);
{
    x = y;
}

// Writing through a ref local that aliases the parameter
ghost function ref_local_bad(ref x: i32[], y: i32[])
{
    ref r = x;
    r = y;        // Error
}

// Swapping with a ghost copy (parameter on the right)
ghost function swap_copy_bad(ref x: i32[], y: i32[])
{
    var c = y;
    swap c, x;    // Error
}

// Ghost vars of incomplete type are copies, not views, so they may change size
ghost function copy_ok(x: i32[], y: i32[])
{
    var c = x;
    var d = y;
    c = y;        // c may change size: it is a copy, not a view
    swap c, d;    // likewise for swap
}

// Element writes do not change the size
function elem_ok(ref x: i32[])
    requires sizeof(x) > u64(0);
    ensures sizeof(x) == old(sizeof(x));
{
    x[0] = 1;
}

// The size is preserved when the parameter is passed on to another function,
// even though that function has no postcondition about the size
extern function ext(ref x: i32[]);

function pass_on(ref x: i32[])
    ensures sizeof(x) == old(sizeof(x));
{
    ext(x);
}

// The caller may assume that the size of a resizable array is unchanged
function call_resizable()
{
    var a: i32[*];
    alloc_array<i32>(a, u64(5));
    ext(a);
    assert sizeof(a) == u64(5);
    free_array<i32>(a);
}
