module Chaining

interface {}

function test()
{
    // Examples of illegal chaining
    var x1 = 1 < 2 > 3;
    var x2 = 1 <= 2 == 3 > 4;
    var x3 = 1 == 2 == 3 < 4 < 5 == 6 > 7;
    var x4 = (1 < 2 > 3) ==> false;   // illegal chaining in sub-expression
    
    // Illegal mixture of <== and ==>
    var y1 = true <== false ==> true;
    var y2 = true ==> false <== true;
    var y3 = true ==> true ==> true <== false;
}
