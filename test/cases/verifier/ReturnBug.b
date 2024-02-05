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
