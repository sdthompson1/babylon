module Division

interface {
    function main();
}

import Test;

// A regression test for division

function main()
{
    var v = 64;
    var d = v/4;
    print_i32(d);
}
