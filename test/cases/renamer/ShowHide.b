module ShowHide

interface {}

function test()
{
    hide foo;  // error
    show foo;  // error
}
