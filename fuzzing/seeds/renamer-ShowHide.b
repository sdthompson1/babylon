module Main

interface {}

function test()
{
    hide foo;  // error
    show foo;  // error
}
