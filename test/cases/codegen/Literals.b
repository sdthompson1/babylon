module Literals

interface {
    function main();
}

import Test;

// Hex and character literals

function main()
{
    Test.print_i32(0x1234);
    Test.print_i32(0x12345678);
    Test.print_i64(0xabcdABCD);
    Test.print_u64(0xffffffffffffffff);
}
