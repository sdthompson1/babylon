module Tuple

// Tuple codegen

interface { function main(); }
import Test;

const t: {i32,i8,i16} = {10, i8(20), i16(30)};

function tuple_test(): {i32, i32}
{
    return {1, 2};
}

function main()
{
    Test.print_i32(t.0);
    Test.print_i8(t.1);
    Test.print_i16(t.2);

    Test.print_i32(tuple_test().1);

    Test.print_i32({10,20,30,40}.2);
}
