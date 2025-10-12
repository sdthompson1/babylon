module Main
interface {}

function f1()
{
    // Error: Ref variable to non-lvalue
    ref y: i32 = 100;

    // Error: ref to wrong type (casting is not allowed for refs)
    var v: i32;
    ref r: i16 = v;
}
