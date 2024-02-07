module Main

interface {}

// Testing typedefs, i.e. we want to make sure that a function reverifies
// when a typedef that it depends on changes.

type MyType = i32;

function f(): MyType
{
    return 1 + 1;
}
