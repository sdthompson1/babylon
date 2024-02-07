module Main

// First run -- Everything should validate, nothing is cached
// (apart from some "end of function unreachable" problems which are trivial
// and identical for each function!).

interface {}

function f(): i32
{
    return 1;
}

function g(): i32
{
    return 1 / f();
}

function h(): i32
{
    return 1 + g();
}

function i(): i32
{
    return 2;
}
