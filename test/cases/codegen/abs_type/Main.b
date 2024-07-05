module Main

interface {
    function main();
}

import Test;
import AbsType;

function main()
{
    var a: AbsType = make_abs();
    set_value(a, 100);
    print_i32(get_value(a));
}
