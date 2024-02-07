module Main

interface {}

// Here we leave the typedef the same (but add a new const) - nothing should reverify.

type MyType = i32;

const NEW_CONST = 99;

function f(): MyType
{
    return 1 + 1;
}
