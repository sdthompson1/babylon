// Example 11 - Allocated.

module Example11

interface {
    impure function main();
}

import Array;
import Console;


// Recall from Example05 that we were able to resize arrays at runtime.
// When an array is resized (above zero), memory is allocated to hold the
// array elements. When the array is resized back to zero, the memory is freed.
// It is a requirement that all arrays should be freed before the function
// returns.

// There are some other restrictions as well. For example, it is not allowed
// to copy an allocated array into another array, because this would need to
// allocate more memory -- and the only way to allocate memory is to use the
// alloc_array function.

// (This might seem a severe restriction, but it at least makes all memory
// allocation operations explicit in the code.)

impure function fun1()
{
    var a: i32[*];
    var ok = alloc_array(a, 100);
    if !ok { return; }

    // var b = a;    // Not allowed, trying to copy an allocated array

    // However, copying a zero-sized array is allowed.
    // This is because the copy will not require any new memory to be
    // allocated.
    free_array(a);
    var b = a;    // Allowed, b is now an empty array of type i32[*].

    assert sizeof(a) == 0;
    assert sizeof(b) == 0;
}


// Returning an allocated value is also not allowed (at least, not in
// the current version of the language). For example the following function
// would not work.

// impure function make_array(): i32[*]
// {
//     var a: i32[*];
//     var ok = alloc_array(a, 10);
//
//     ... check for memory allocation failure omitted ...
//
//     var i = 0;
//     while i < 10
//         ... invariants and decreases omitted ...
//     {
//         a[i] = i;
//         i = i + 1;
//     }
// 
//     return a;   // Doesn't work, returning an allocated value is not allowed.
// }

// A workaround is to use a "ref" parameter, as follows.
// (Note that memory allocation might fail, so we return a bool to let the caller
// know whether we were successful or not.)
impure function make_array(ref a: i32[*]): bool
    requires sizeof(a) == 0;
    ensures return ==> sizeof(a) == 10;
    ensures return ==> (forall (i: i32) 0 <= i < 10 ==> a[i] == i);
    ensures !return ==> sizeof(a) == 0;
{
    var ok = alloc_array(a, 10);

    if !ok {
        return false;
    }

    var i = 0;
    while i < 10
        invariant 0 <= i <= 10;
        invariant sizeof(a) == 10;
        invariant forall (j: i32) 0 <= j < i ==> a[j] == j;
        decreases ~i;
    {
        a[i] = i;
        i = i + 1;
    }

    return true;
}

// Now we can use the make_array function as follows.
impure function fun2()
{
    var a: i32[*];
    var ok = make_array(a);
    if !ok { return; }

    print_i32(a[7]);   // prints 7
    println("");

    // Because a was allocated by make_array, it must now be freed.
    free_array(a);
}


// Swapping of allocated values is allowed (and is sometimes useful).
impure function fun3()
{
    var a: i32[*];
    var b: i32[*];

    var ok = alloc_array(a, 10);
    if !ok { return; }
    
    ok = alloc_array(b, 5);
    if !ok { free_array(a); return; }

    a[2] = 2;
    b[3] = 3;

    swap a, b;   // This is fine

    assert sizeof(a) == 5;
    assert a[3] == 3;
    assert sizeof(b) == 10;
    assert b[2] == 2;

    free_array(a);
    free_array(b);
}


// It is possible to use the "allocated" keyword to ask whether a value is
// allocated or not.

impure function fun4()
{
    // Integers and booleans are not considered allocated.
    assert !allocated(123);

    // An array is allocated if and only if its size is nonzero.
    var a: i32[*];
    assert !allocated(a);

    var ok = alloc_array(a, 10);
    if !ok { return; }
    
    assert allocated(a);

    free_array(a);

    // A tuple or record is allocated if any of its components are.
    var t: {i32[*], bool, i32};
    assert !allocated(t);

    ok = alloc_array(t.0, 10);
    if !ok { return; }
    
    t.1 = true;

    assert allocated(t);

    free_array(t.0);
}


// "allocated" is sometimes useful in function preconditions. The following
// function returns a record which is a modified version of the input record.
// Because returning allocated values is not allowed, it requires that the
// input record is not allocated.

function fun5(x: {a1: i32[*], a2: i32[*], b: bool, i: i32})
        : {a1: i32[*], a2: i32[*], b: bool, i: i32}
    requires !allocated(x);
{
    // If x was allocated then the following would not work, but because
    // of the precondition, the verifier is able to confirm that the array
    // is non-allocated, therefore the return statement is allowed.
    return {x with b=true, i=42};
}

// Admittedly the above example "fun5" is a little contrived, but we will see
// a more useful example of "allocated" in the next example.


// Note: "allocated" cannot be used in executable code; it can only be used in
// verification contexts (asserts and preconditions and the like).

// However, you *can* call "sizeof" in executable code, so e.g. if you need to
// check at runtime whether an array is allocated, you can use something like
// "sizeof(a) == 0" or "sizeof(a) != 0".


impure function main()
{
    fun2();
}
