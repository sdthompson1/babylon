module ElseIf
interface { function main(); }

import Test;

function sgn(x: i32): i32
{
    if (x < 0) {
        return -1;
    } else if (x == 0) {
        return 0;
    } else {
        return 1;
    }
}

function main()
{
    Test.print_i32(sgn(-203));
    Test.print_i32(sgn(0));
    Test.print_i32(sgn(1807));
}
