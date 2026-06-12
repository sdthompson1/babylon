module GhostRef

// Tests for 'ref' local variable declarations in ghost code.

interface {}

function f()
{
    var v: i32 = 50;
    ghost var g: i32 = 100;
    ghost var a: i32[10];

    ghost ref r1 = g;       // OK, ghost ref to ghost variable
    ghost r1 = 200;         // OK, writing to ghost variable via ghost ref

    ghost ref r2 = a[4];    // OK, ghost ref to element of ghost array
    ghost r2 = 5;           // OK

    ghost ref r3 = v;       // Error, a ref in ghost code must refer to a ghost variable

    assert (1 == 1)
    {
        ref r4 = v;         // Error, refs in proof code are ghost, so must refer to a ghost variable
        ref r5 = g;         // OK, ref to ghost variable in proof code
    }
}

// In a ghost function, all parameters and locals are ghost, so refs to them are fine.
ghost function gf(x: i32)
{
    ref r = x;              // OK
    var y: i32 = 10;
    ref s = y;              // OK
}

// 'ref' patterns in ghost match statements follow the same rule.
datatype D = Mk(i32);

function g()
{
    var v: D = Mk(50);
    ghost var w: D = Mk(50);

    ghost match w {
    case Mk(ref x) =>       // OK, ref pattern over ghost scrutinee
        x = 99;
    }

    ghost match v {
    case Mk(ref x) =>       // Error, ref pattern over non-ghost scrutinee in ghost code
    }

    // In a match *term*, ref patterns cannot be written through, so they are
    // allowed over non-ghost scrutinees even in proof code.
    assert (match v { case Mk(ref x) => x == 50 });   // OK
}
