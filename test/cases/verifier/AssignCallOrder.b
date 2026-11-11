module AssignCallOrder

// An assignment evaluates its right-hand side first, and only then resolves
// its left-hand side. So when the right-hand side is a call that modifies a
// variable used in the left-hand side, it is the state *after* the call
// that decides which element is written, and whether it is in bounds.
// (See also test/cases/codegen/AssignCallOrder.b.)

interface {}

function set(ref i: u64, new_i: u64): i32
    ensures i == new_i;
    ensures return == 1;
{
    i = new_i;
    return 1;
}

function f1(ref i: u64)
    requires i == 20;
{
    var a: i32[10];
    a[i] = set(i, 3);      // OK: in bounds after the call
    assert a[3] == 1;
}

function f2(ref i: u64)
    requires i == 3;
{
    var a: i32[10];
    a[i] = set(i, 20);     // Error: out of bounds after the call
}

function f3()
{
    var i: u64 = 3;
    var a: i32[10];
    a[i] = set(i, 4);
    assert a[4] == 1;
    assert a[3] == 0;
    assert a[3] == 1;      // Error: a[3] was not written
}

function f4(ref i: u64)
    requires i == 3;
{
    // A reference is resolved when it is declared.
    var a: i32[10];
    ref r = a[i];
    r = set(i, 20);
    assert a[3] == 1;
    assert i == 20;
}
