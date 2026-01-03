module GhostArgOnly
interface { function main(); }
import Test;

ghost function ghost_only(ghost x: i32, ghost y: i32): i32
    requires -100 < x < 100;
    requires -100 < y < 100;
{
    return x + y;
}

function has_ghost_args(ghost x: i32): i32
{
    return 42;  // ghost arg not used in executable code
}

function main()
{
    var v = has_ghost_args(999);
    Test.print_i32(v);  // Should print 42
}
