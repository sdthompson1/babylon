module Ghost

// Check that ghost code is not executed

interface { function main(); }

import Test;

// Ghost function -- codegen will skip the entire function
ghost function ghost_example(): bool
{
    return forall (x:i32) x > 0;    // Equals false, but this cannot be compiled to executable code
}
ghost const ghost_example_value: bool = ghost_example();


// Function with ghost vars and ghost assignments, which will be skipped,
// but the rest of the function executes
function ghost_stmts(): i32
{
    var x: i32 = 100;
    ghost var y: bool = forall (z:i32) z == 0;
    ghost y = false;
    obtain (z:i32) z > 0;
    return x;
}


function main()
{
    Test.print_i32(ghost_stmts());
}
