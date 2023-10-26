module StackAlign

// Testing some cases where stack alignment is important

interface { function main(); }

import Test;

function print0<a>()
    requires !allocated(default<a>());
{
    // Test that the stack remains aligned after a variable
    // sized memory block is created. (Failing to align the
    // stack causes printf to crash, at least on my machine.)
    var x: a;
    Test.print_i32(0);
}

function args(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32, g: i32)
{
    // On Linux x86, a 7-argument function means one 8-byte arg
    // is pushed to the stack (the first 6 args being passed in
    // registers), so the compiler needs to offset the stack by
    // another 8 bytes to keep it 16-byte aligned as we require.
    Test.print_i32(1);
}

function main()
{
    print0<i32>();
    print0<i64>();
    print0<{i64,i64,i64,i64,i64}>();
    args(1,2,3,4,5,6,7);
}
