module ConstVariant
interface {
    function main();
}

// A const object that needs some padding bytes in the middle of it.

import Test;

datatype Variant = Big(i32) | Small(i16);

// represented as: [tag byte, 2 payload bytes, 2 pad bytes, 4 bytes for the "1000"].
const padded = {Small(123), 1000};

function main()
{
    match padded {
    case {Small(x), y} =>
        Test.print_i16(x);
        Test.print_i32(y);
    }
}
