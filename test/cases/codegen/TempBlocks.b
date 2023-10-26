module TempBlocks

interface {
    function main();
}

import Test;

// Regression test for a bug involving (mis-)use of temp mem blocks
// during assignment statements.

function main()
{
    var foo: i32[];
    resize_array<i32>(foo, 10);
    
    foo[{x=1}.x] = {x=2,y=3,z=4,a=5,b=6,c=7}.x;
    print_i32(foo[1]);
    
    resize_array<i32>(foo, 0);
}

