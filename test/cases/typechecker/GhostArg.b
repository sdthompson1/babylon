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

// A ghost arg is erased before codegen, so its declared type does not
// have to be a runtime type -- even though this function is not ghost.
function nonruntime_args(ghost a: int,
                         ghost b: real,
                         ghost ref c: int,
                         ghost d: {i32, int})   // 'int' nested inside a tuple
{
    ghost c = c + a + d.1;
}

function call_nonruntime_args()
{
    ghost var n: int = int(0);
    ghost nonruntime_args(int(1), real(2), n, {5, int(3)});
}

// ... but a non-ghost arg still may not have a non-runtime type.
function runtime_args(a: int, b: real)  // Two errors
{}
