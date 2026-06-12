module GhostRef
interface { function main(); }
import Test;

// Check that 'ghost ref' local variables exist for verification
// but produce no executable code.

datatype D = Mk(i32);

function main()
{
    var x: i32 = 100;

    ghost var a: i32[10];
    ghost ref r = a[4];
    ghost r = 25;           // only affects verification
    assert a[4] == 25;

    ghost var g: i32 = 1;
    ghost ref s = g;
    ghost s = s + 1;
    assert g == 2;

    // ref patterns in a ghost match statement are also verification-only
    ghost var v: D = Mk(50);
    ghost match v {
    case Mk(ref y) =>
        y = 99;
    }
    assert v == Mk(99);

    x = x + 1;
    Test.print_i32(x);  // Should print 101
}
