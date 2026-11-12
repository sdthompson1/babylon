module SwapOrder

// A swap resolves both of its operands to places first (evaluating any
// array indexes), and only then exchanges the contents of the two places.
// So when one operand is used in an index of the other, it is the state
// *before* the swap that decides which element is exchanged, and whether
// the index is in bounds.
// (See also test/cases/codegen/SwapOrder.b.)

interface {}

function f1()
{
    var a: u64[10];
    var i: u64 = 2;
    a[2] = 7;
    a[7] = 100;
    swap i, a[i];
    assert i == 7;
    assert a[2] == 2;
    assert a[7] == 100;
    assert a[7] == 2;      // Error: a[7] was not written
}

function f2()
{
    var a: u64[10];
    var i: u64 = 3;
    a[3] = 8;
    a[8] = 200;
    swap a[i], i;
    assert i == 8;
    assert a[3] == 3;
    assert a[8] == 200;
    assert a[8] == 3;      // Error: a[8] was not written
}

function f3()
{
    var a: u64[10];
    var i: u64 = 2;
    a[2] = 20;
    swap i, a[i];          // OK: in bounds before the swap
    assert i == 20;
    assert a[2] == 2;
}

function f4()
{
    var a: u64[10];
    var i: u64 = 20;
    a[2] = 2;
    swap a[i], i;          // Error: out of bounds before the swap
}
