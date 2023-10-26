module Imported
import Int;
    
interface {
    function add(x: i32, y: i32): i32
        requires Int.can_add_i32(x, y);
}

const dummy: i32 = 1000;  // Redundant, but exercises some lines in typechecker.c
datatype DummyData = DummyData;   // Likewise

function add(x: i32, y: i32): i32
    requires Int.can_add_i32(x, y);
{
    return x + y;
}
