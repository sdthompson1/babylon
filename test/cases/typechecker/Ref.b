module Ref
interface {}

function f1()
{
    // Error: Ref variable to non-lvalue
    ref y: i32 = 100;
}
