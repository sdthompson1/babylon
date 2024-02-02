module ExternInImpl

interface {
    function main();
}

import Test;

extern function c_test_fun(): i32;

function main()
{
    print_i32(c_test_fun());
}
