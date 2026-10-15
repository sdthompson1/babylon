module GhostArgExtern

interface {
    function main();
}

import Test;

// Non-ghost extern functions with ghost parameters. The ghost parameters
// are erased from the generated C, so these can be bound to existing C
// functions (from Test.c) that take only the non-ghost parameters.

// Ghost parameters before and after the non-ghost one.
extern function print_checked(ghost lo: int, x: i32, ghost hi: int) = "print_i32"
    requires lo <= int(x) <= hi;

// Ghost ref parameter.
extern function print_ghost_ref(ghost ref g: i32, x: i32) = "print_i32"
    requires g == x;

// Only ghost parameters, so the C function takes no arguments.
extern function get_42(ghost a: bool, ghost b: int): i32 = "c_test_fun"
    requires a;
    ensures return == 42;

function main()
{
    print_checked(int(1), 5, int(10));

    var x: i32 = 7;
    ghost var g: i32 = 7;
    print_ghost_ref(g, x);

    var r = get_42(true, int(0));
    print_i32(r);
}
