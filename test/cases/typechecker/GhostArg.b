module GhostArg
interface {}

function f(ghost x: i32, ghost ref y: i32)
{
    ghost var temp = x + 1; // OK, can read ghost arg in ghost code
    ghost y = y + 1;        // OK, ghost ref arg can be modified
}

function test()
{
    var v: i32 = 10;
    ghost var g: i32 = 20;

    f(v, g);          // OK, non-ref ghost arg accepts any value
    f(g, g);          // OK
    f(100, g);        // OK, literals work too
    f(v, v);          // Error: ref ghost arg requires ghost lvalue
}

ghost function ghost_fn(ghost x: i32, ref y: i32)  // OK, ghost function
{}

function exec_fn(ghost x: i32)  // OK, executable function with ghost arg
{
    ghost var temp = x + 1;    // OK, can use ghost arg in ghost code
    var v = x;                 // Error: can't use ghost arg in executable code
}
