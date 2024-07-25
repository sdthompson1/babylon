module ReturnBug

interface {}

// Regression test for a previous crash bug
// (return after another return)
function f1(x: i32): i32
{
    return 1;
    if (x == 0) {
        return 2;
    }
}

function f2()
{
    assert false;  // Force verification failure
}


// Another (previous) bug - incorrect verification after
// a return stmt calling a fn with a ref arg.

function my_fn(ref x: i32): i32
{
    x = 1;
    return 1;
}

function f3(b: bool): i32
{
    var x = 0;
    if b {
        return my_fn(x);
    }
    assert x == 0;  // should succeed
    return 0;
}
