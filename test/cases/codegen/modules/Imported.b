module Imported

import Test;

interface {
    function add(x: i32, y: i32): i32
        requires int(I32_MIN) <= int(x) + int(y) <= int(I32_MAX);
}

const dummy: i32 = 1000;  // Redundant, but exercises some lines in typechecker.c
datatype DummyData = DummyData;   // Likewise

function add(x: i32, y: i32): i32
    requires int(I32_MIN) <= int(x) + int(y) <= int(I32_MAX);
{
    return x + y;
}
