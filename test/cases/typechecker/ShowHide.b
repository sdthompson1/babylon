module ShowHide

interface {}

function test()
{
    var x: i32;
    show x;  // error, can't show/hide non-function value
    hide x;  // ditto
}

function test2()
{
    var y = 1 + false;   // error
    hide y;   // doesn't generate error because x's type is unknown/invalid
}
