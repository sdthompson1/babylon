module Main

// Second run - entire module will hit the cache and be skipped.

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
