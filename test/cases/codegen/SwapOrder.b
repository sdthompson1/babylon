module SwapOrder

// "swap e1, e2;" first resolves both of its operands to places (evaluating
// any array indexes), and only then exchanges the contents of the two
// places. So in "swap i, a[i];" the element exchanged with i is the one
// selected by the value of i *before* the swap, and likewise in
// "swap a[i], i;".
//
// This is what the verifier assumes. Each case below asserts what the
// verifier believes and then prints the same values, so that the compiled
// code is checked against the verifier's view.

interface { function main(); }
import Test;

type Cell = {idx: u64, val: i32};

// The index is a local variable, which is also the other operand.
function local_index()
{
    var a: u64[10];
    var i: u64 = 2;
    a[2] = 7;
    a[7] = 100;
    swap i, a[i];
    assert i == 7;
    assert a[2] == 2;
    assert a[7] == 100;
    print_u64(i);      // 7
    print_u64(a[2]);   // 2
    print_u64(a[7]);   // 100

    var j: u64 = 3;
    a[3] = 8;
    a[8] = 200;
    swap a[j], j;
    assert j == 8;
    assert a[3] == 3;
    assert a[8] == 200;
    print_u64(j);      // 8
    print_u64(a[3]);   // 3
    print_u64(a[8]);   // 200
}

// The same, but the index and the array are ref parameters.
function ref_index(ref i: u64, ref a: u64[10])
    requires i == 2;
    requires a[2] == 7;
    requires a[7] == 100;
{
    swap i, a[i];
    assert i == 7;
    assert a[2] == 2;
    assert a[7] == 100;
    print_u64(i);      // 7
    print_u64(a[2]);   // 2
    print_u64(a[7]);   // 100

    a[7] = 4;
    a[4] = 300;
    swap a[i], i;
    assert i == 4;
    assert a[7] == 7;
    assert a[4] == 300;
    print_u64(i);      // 4
    print_u64(a[7]);   // 7
    print_u64(a[4]);   // 300
}

// The array is allocatable (its elements are reached through a descriptor).
function alloc_index()
{
    var a: u64[*];
    alloc_array(a, 10);
    var i: u64 = 2;
    a[2] = 7;
    a[7] = 100;
    swap i, a[i];
    assert i == 7;
    assert a[2] == 2;
    assert a[7] == 100;
    print_u64(i);      // 7
    print_u64(a[2]);   // 2
    print_u64(a[7]);   // 100

    a[7] = 5;
    a[5] = 400;
    swap a[i], i;
    assert i == 5;
    assert a[7] == 7;
    assert a[5] == 400;
    print_u64(i);      // 5
    print_u64(a[7]);   // 7
    print_u64(a[5]);   // 400
    free_array(a);
}

// The index is an element of the same array.
function self_index()
{
    var a: u64[10];
    a[0] = 5;
    a[5] = 9;
    a[9] = 500;
    swap a[0], a[a[0]];
    assert a[0] == 9;
    assert a[5] == 5;
    assert a[9] == 500;
    print_u64(a[0]);   // 9
    print_u64(a[5]);   // 5
    print_u64(a[9]);   // 500

    a[0] = 6;
    a[6] = 1;
    a[1] = 600;
    swap a[a[0]], a[0];
    assert a[0] == 1;
    assert a[6] == 6;
    assert a[1] == 600;
    print_u64(a[0]);   // 1
    print_u64(a[6]);   // 6
    print_u64(a[1]);   // 600
}

// The index is a field of the other operand (an aggregate).
function field_index()
{
    var a: Cell[10];
    var c: Cell = {idx = u64(2), val = 10};
    a[2] = {idx = u64(7), val = 20};
    a[7] = {idx = u64(0), val = 30};
    swap c, a[c.idx];
    assert c == {idx = u64(7), val = 20};
    assert a[2] == {idx = u64(2), val = 10};
    assert a[7] == {idx = u64(0), val = 30};
    print_u64(c.idx);      // 7
    print_i32(c.val);      // 20
    print_u64(a[2].idx);   // 2
    print_i32(a[2].val);   // 10
    print_u64(a[7].idx);   // 0
    print_i32(a[7].val);   // 30

    a[7] = {idx = u64(4), val = 40};
    a[4] = {idx = u64(0), val = 50};
    swap a[c.idx], c;
    assert c == {idx = u64(4), val = 40};
    assert a[7] == {idx = u64(7), val = 20};
    assert a[4] == {idx = u64(0), val = 50};
    print_u64(c.idx);      // 4
    print_i32(c.val);      // 40
    print_u64(a[7].idx);   // 7
    print_i32(a[7].val);   // 20
    print_u64(a[4].idx);   // 0
    print_i32(a[4].val);   // 50
}

// Two indexes, one of which is the other operand.
function two_dim()
{
    var m: u64[3, 3];
    var i: u64 = 1;
    m[1, 2] = 2;
    m[2, 2] = 700;
    swap i, m[i, 2];
    assert i == 2;
    assert m[1, 2] == 1;
    assert m[2, 2] == 700;
    print_u64(i);         // 2
    print_u64(m[1, 2]);   // 1
    print_u64(m[2, 2]);   // 700

    m[2, 0] = 1;
    m[1, 0] = 800;
    swap m[i, 0], i;
    assert i == 1;
    assert m[2, 0] == 2;
    assert m[1, 0] == 800;
    print_u64(i);         // 1
    print_u64(m[2, 0]);   // 2
    print_u64(m[1, 0]);   // 800
}

// The operands are allocatable arrays, and the index of one of them is
// read from the other: after the swap, "idx" is a different array.
function array_operands()
{
    var idx: u64[*];
    var data: u64[3][*];
    alloc_array(idx, 2);
    alloc_array(data[1], 2);
    alloc_array(data[2], 2);
    idx[0] = 1;
    idx[1] = 11;
    data[1][0] = 2;
    data[1][1] = 22;
    data[2][0] = 0;
    data[2][1] = 33;

    swap idx, data[idx[0]];
    assert idx[0] == 2 && idx[1] == 22;
    assert data[1][0] == 1 && data[1][1] == 11;
    assert data[2][0] == 0 && data[2][1] == 33;
    print_u64(idx[1]);       // 22
    print_u64(data[1][1]);   // 11
    print_u64(data[2][1]);   // 33

    swap data[idx[0]], idx;
    assert idx[0] == 0 && idx[1] == 33;
    assert data[1][0] == 1 && data[1][1] == 11;
    assert data[2][0] == 2 && data[2][1] == 22;
    print_u64(idx[1]);       // 33
    print_u64(data[1][1]);   // 11
    print_u64(data[2][1]);   // 22

    free_array(idx);
    free_array(data[1]);
    free_array(data[2]);
}

// A reference is resolved when it is declared, so swapping through it is
// not affected by a change to the index.
function ref_operand()
{
    var a: u64[*];
    alloc_array(a, 10);
    var i: u64 = 2;
    a[2] = 7;
    a[7] = 900;
    ref r = a[i];
    swap i, r;
    assert i == 7;
    assert a[2] == 2;
    assert a[7] == 900;
    print_u64(i);      // 7
    print_u64(a[2]);   // 2
    print_u64(a[7]);   // 900

    swap r, i;
    assert i == 2;
    assert a[2] == 7;
    assert a[7] == 900;
    print_u64(i);      // 2
    print_u64(a[2]);   // 7
    print_u64(a[7]);   // 900
    free_array(a);
}

function main()
{
    local_index();

    var i: u64 = 2;
    var a: u64[10];
    a[2] = 7;
    a[7] = 100;
    ref_index(i, a);

    alloc_index();
    self_index();
    field_index();
    two_dim();
    array_operands();
    ref_operand();
}
