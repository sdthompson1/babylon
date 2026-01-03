module GhostArg
interface {}

function add_with_witness(x: i32, ghost witness: i32, y: i32): i32
    requires int(witness) == int(x) + int(y);
    ensures return == witness;
{
    // The witness proves that x+y won't overflow (since witness is a valid i32)
    return x + y;
}

function test1()
{
    var v = add_with_witness(3, 7, 4);
    assert v == 7;  // OK
}

function test2()
{
    var v = add_with_witness(3, 8, 4);  // Error: witness doesn't match
    assert v == 7;
}

function swap_vars(ref x: i32, ref y: i32, ghost ref diff: i32)
    requires -1000 < x < 1000;
    requires -1000 < y < 1000;
    requires diff == x - y;
    ensures x == old(y);
    ensures y == old(x);
    ensures diff == x - y;  // diff gets updated correctly (sign flips)
{
    var tmp = x;
    x = y;
    y = tmp;
    ghost diff = x - y;
}

function test_swap()
{
    var a = 10;
    var b = 5;
    ghost var d = 5;  // 10 - 5
    swap_vars(a, b, d);
    assert a == 5;   // OK
    assert b == 10;  // OK
    assert d == -5;  // OK (sign flipped: 5 - 10)
}
