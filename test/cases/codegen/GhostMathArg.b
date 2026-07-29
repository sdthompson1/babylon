module GhostMathArg
interface { function main(); }
import Test;

// A ghost argument is erased before code generation, so it is allowed
// to have a non-runtime type ('int' here), even though "add" itself is
// not a ghost function. Here "sum" is a "witness" argument, used only
// to state the specification.
function add(x: i32, ghost sum: int, y: i32): i32
    requires sum == int(x) + int(y);
    requires int(I32_MIN) <= sum <= int(I32_MAX);
    ensures int(return) == sum;
{
    return x + y;
}

// Ghost 'real' argument, plus a ghost 'ref' argument of non-runtime type.
function accumulate(x: i32, ghost scale: real, ghost ref total: int)
    ensures total == old(total) + int(x);
{
    ghost total = total + int(x);
}

// A ghost argument whose non-runtime type is buried inside a tuple.
function tuple_arg(x: i32, ghost pair: {int, i32}): i32
    requires pair.0 == int(x);
    ensures int(return) == pair.0;
{
    return x;
}

function main()
{
    print_i32(add(3, int(7), 4));      // 7

    ghost var total: int = int(0);
    accumulate(5, real(2), total);
    accumulate(6, real(3), total);
    assert total == int(11);

    print_i32(tuple_arg(9, {int(9), 0}));  // 9
}
