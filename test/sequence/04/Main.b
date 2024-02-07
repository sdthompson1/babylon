module Main

// Here we change f, which should cause g and h to be reverified,
// but i is still skipped because it does not depend (directly
// or indirectly) on f.

interface {}

const A_NEW_CONSTANT = 1;

function f(): i32
{
    return 2;
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
