module Arrays4

interface {}

function f_sized(a: i32[10], b: i32[10,20])
{ }

function test()
{
    var s1: i32[10];
    f_sized(s1, s1);   // type error, 2nd argument doesn't match i32[10,20]
}
