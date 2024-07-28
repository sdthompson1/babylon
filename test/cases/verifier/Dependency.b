module Dependency

// Regression test for a dependency analysis bug. See issue #10.

interface {
    function integer_in_range(x: i32): bool
    {
        return integer_in_range_impl(x);
    }

    function integer_in_range_impl(x: i32): bool;
}

// This was previously failing to verify because it was not
// looking at the implementation of integer_in_range_impl.
ghost function my_theorem()
    ensures integer_in_range(42); // should succeed
{}

ghost function my_theorem_2()
    ensures integer_in_range(0);  // should fail
{}

function integer_in_range_impl(x: i32): bool
{
    return 30 <= x <= 50;
}
