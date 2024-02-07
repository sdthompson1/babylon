module Main

interface {}

// Here we change the typedef. f should reverify.

type MyType = i64;

function f(): MyType
{
    return 1 + 1;
}
