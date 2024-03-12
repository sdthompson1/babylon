module Equality

interface {}

const str1 = "hello  ";
const str2 = "goodbye";

function f1()
{
    assert {str1, str2} == {str1, str2};
    assert {str1, 99} == {str2, 99};    // Error
}

datatype X = X(u8[3]) | Y(i32);

const gx = X("foo");
const gx2 = X("bar");

function f2()
{
    assert gx == gx;
    assert Y(1) == Y(2-1);
    assert gx != Y(1);
    assert gx == gx2;    // Error
}
