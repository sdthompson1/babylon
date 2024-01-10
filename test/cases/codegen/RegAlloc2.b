module RegAlloc2

// Regression test for an infinite loop in the reconciler.

interface {
    function main();
}

function f(a: i32, b: {i32}, c: i32)
{}

function test(a: i32, b: {i32}, c: i32)
{
    if true {
        var b_new = {99};
        f(a, b_new, c);
    } else {
        f(a, b, c);
    }
}

function main()
{
}
