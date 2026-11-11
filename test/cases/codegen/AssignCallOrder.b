module AssignCallOrder

// An assignment evaluates its right-hand side first, and only then resolves
// its left-hand side. So in "a[i] = f(i);", where the call f(i) modifies i,
// the element written is the one selected by the value of i *after* the call.
//
// This is the order that the verifier assumes. Each case below asserts what
// the verifier believes and then prints the same values, so that the
// compiled code is checked against the verifier's view.

interface { function main(); }
import Test;

type Pair = {x: i32, y: i32};

// Set i to new_i, and return r.
function set_i32(ref i: u64, new_i: u64, r: i32): i32
    ensures i == new_i;
    ensures return == r;
{
    i = new_i;
    return r;
}

// The same, but the result is an aggregate (returned through a buffer).
function set_pair(ref i: u64, new_i: u64, x: i32, y: i32): Pair
    ensures i == new_i;
    ensures return == {x = x, y = y};
{
    i = new_i;
    return {x = x, y = y};
}

// Set both i and j.
function set_two(ref i: u64, ref j: u64, new_i: u64, new_j: u64, r: i32): i32
    ensures i == new_i;
    ensures j == new_j;
    ensures return == r;
{
    i = new_i;
    j = new_j;
    return r;
}

// Allocate the array, and return r.
function alloc_ret(ref a: i32[*], r: i32): i32
    requires sizeof(a) == u64(0);
    ensures sizeof(a) == u64(10);
    ensures forall (j: u64) j < 10 ==> a[j] == 0;
    ensures return == r;
{
    alloc_array(a, 10);
    return r;
}


// The index is a ref parameter, which the call modifies.
function ref_index(ref i: u64)
    requires i == 5;
{
    var a: i32[10];
    a[i] = set_i32(i, 2, 123);
    assert a[2] == 123;
    assert a[5] == 0;
    print_i32(a[2]);   // 123
    print_i32(a[5]);   // 0
}

// The index is a local variable, which the call modifies.
function local_index()
{
    var i: u64 = 5;
    var a: i32[10];
    a[i] = set_i32(i, 2, 124);
    assert a[2] == 124;
    assert a[5] == 0;
    print_i32(a[2]);   // 124
    print_i32(a[5]);   // 0
}

// The result of the call is implicitly cast (i32 to i64).
function cast_ref_index(ref i: u64)
    requires i == 5;
{
    var a: i64[10];
    a[i] = set_i32(i, 2, 125);
    assert a[2] == 125;
    assert a[5] == 0;
    print_i64(a[2]);   // 125
    print_i64(a[5]);   // 0
}

function cast_local_index()
{
    var i: u64 = 5;
    var a: i64[10];
    a[i] = set_i32(i, 2, 126);
    assert a[2] == 126;
    assert a[5] == 0;
    print_i64(a[2]);   // 126
    print_i64(a[5]);   // 0
}

// A longer lvalue: a field of a record in an array.
function record_field(ref i: u64)
    requires i == 5;
{
    var a: Pair[10];
    a[i].y = set_i32(i, 2, 127);
    assert a[2].y == 127;
    assert a[5].y == 0;
    print_i32(a[2].y);   // 127
    print_i32(a[5].y);   // 0

    var j: u64 = 7;
    a[j].x = set_i32(j, 3, 128);
    assert a[3].x == 128;
    assert a[7].x == 0;
    print_i32(a[3].x);   // 128
    print_i32(a[7].x);   // 0
}

// A two-dimensional array; one index is a ref parameter and the other is a
// local, and the call modifies both. The index expressions are not just
// variables.
function two_dim(ref i: u64)
    requires i == 3;
{
    var j: u64 = 4;
    var a: i32[4,6];
    a[i - 1, j + 1] = set_two(i, j, 1, 2, 129);
    assert a[0, 3] == 129;
    assert a[2, 5] == 0;
    print_i32(a[0, 3]);   // 129
    print_i32(a[2, 5]);   // 0
}

// An aggregate result (a record, returned through a buffer).
function aggregate_result(ref i: u64)
    requires i == 5;
{
    var a: Pair[10];
    a[i] = set_pair(i, 2, 11, 22);
    assert a[2] == {x = 11, y = 22};
    assert a[5] == {x = 0, y = 0};
    print_i32(a[2].x);   // 11
    print_i32(a[2].y);   // 22
    print_i32(a[5].x);   // 0
    print_i32(a[5].y);   // 0

    var j: u64 = 7;
    a[j] = set_pair(j, 3, 33, 44);
    assert a[3] == {x = 33, y = 44};
    assert a[7] == {x = 0, y = 0};
    print_i32(a[3].x);   // 33
    print_i32(a[3].y);   // 44
    print_i32(a[7].x);   // 0
    print_i32(a[7].y);   // 0
}

// A "ref" local is different: it is resolved when it is declared. So here
// the store goes to the element selected when r was declared, whatever the
// call does to i afterwards.
function ref_local(ref i: u64)
    requires i == 5;
{
    var a: i32[10];
    ref r = a[i];
    r = set_i32(i, 2, 130);
    assert a[5] == 130;
    assert a[2] == 0;
    print_i32(a[2]);   // 0
    print_i32(a[5]);   // 130

    var j: u64 = 7;
    ref s = a[j];
    s = set_i32(j, 3, 131);
    assert a[7] == 131;
    assert a[3] == 0;
    print_i32(a[3]);   // 0
    print_i32(a[7]);   // 131
}

// The array that the left-hand side indexes is allocated by the call: the
// left-hand side would be out of bounds before the call, but is in bounds
// after it.
function alloc_by_call()
{
    var a: i32[*];
    a[3] = alloc_ret(a, 132);
    assert a[3] == 132;
    assert a[4] == 0;
    print_i32(a[3]);   // 132
    print_i32(a[4]);   // 0
    free_array(a);
}

// The index is far out of bounds before the call, and in bounds after it.
function zero(ref i: u64): i32
    ensures i == 0;
{
    i = 0;
    return 133;
}

function out_of_bounds_before(ref i: u64)
{
    var a: i32[10];
    a[i] = zero(i);
    assert a[0] == 133;
    print_i32(a[0]);   // 133
}

function main()
{
    var i: u64 = 5;
    ref_index(i);
    local_index();
    i = 5;
    cast_ref_index(i);
    cast_local_index();
    i = 5;
    record_field(i);
    i = 3;
    two_dim(i);
    i = 5;
    aggregate_result(i);
    i = 5;
    ref_local(i);
    alloc_by_call();
    i = 99999999;
    out_of_bounds_before(i);
}
