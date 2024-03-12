
// This is the eleventh demonstration program for the Babylon language.

// In this file we explain the rules around "allocated" values.


module Demo_11_Allocated

interface {
    function main();
}

import ExampleLib;


// Recall from Demo_05_Arrays that we were able to resize arrays at runtime.
// When an array is resized (above zero), memory is allocated to hold the
// array elements. When the array is resized back to zero, the memory is freed.
// It is a requirement that all arrays should be freed before the function
// returns.

// There are some other restrictions as well. For example, it is not allowed
// to copy an allocated array into another array, because this would need to
// allocate more memory -- and the only way to allocate memory is to use the
// resize_array function.

// (This might seem a severe restriction, but it at least makes all memory
// allocation operations explicit in the code.)

// (Note that I might change the rules about "allocated" values in future.
// For example, perhaps something like Rust's "move" and "borrow" semantics
// could be used. But this file describes the system that we have at the
// moment.)

function fun1()
{
    var a: i32[*];
    resize_array<i32>(a, 100);

    // var b = a;    // Not allowed, trying to copy an allocated array

    // However, copying a zero-sized array is allowed.
    // This is because the copy will not require any new memory to be
    // allocated.
    resize_array<i32>(a, 0);
    var b = a;    // Allowed, b is now empty.

    assert sizeof(a) == u64(0);
    assert sizeof(b) == u64(0);
}


// Returning an allocated value is also not allowed (at least, not in
// the current version of the language). For example the following function
// would not work.

// function make_array(): i32[*]
// {
//     var a: i32[*];
//     resize_array<i32>(a, 10);
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
function make_array(ref a: i32[*])
    ensures sizeof(a) == u64(10);
    ensures forall (i: i32) 0 <= i < 10 ==> a[i] == i;
{
    resize_array<i32>(a, 10);

    var i = 0;
    while i < 10
        invariant 0 <= i <= 10;
        invariant sizeof(a) == u64(10);
        invariant forall (j: i32) 0 <= j < i ==> a[j] == j;
        decreases ~i;
    {
        a[i] = i;
        i = i + 1;
    }
}

// Now we can use the make_array function as follows.
function fun2()
{
    var a: i32[*];
    make_array(a);

    print_i32(a[7]);   // prints 7
    print_string("\n");

    // Because a was allocated (resized) by make_array, it must now be freed.
    resize_array<i32>(a, 0);
}


// Swapping of allocated values is allowed (and is sometimes useful).
function fun3()
{
    var a: i32[*];
    var b: i32[*];

    resize_array<i32>(a, 10);
    resize_array<i32>(b, 5);

    a[2] = 2;
    b[3] = 3;

    swap a, b;   // This is fine

    assert sizeof(a) == u64(5);
    assert a[3] == 3;
    assert sizeof(b) == u64(10);
    assert b[2] == 2;

    resize_array<i32>(a, 0);
    resize_array<i32>(b, 0);
}


// It is possible to use the "allocated" keyword to ask whether a value is
// allocated or not.

function fun4()
{
    // Integers and booleans are not considered allocated.
    assert !allocated(123);

    // An array is allocated if and only if its size is nonzero.
    var a: i32[*];
    assert !allocated(a);

    resize_array<i32>(a, 10);
    assert allocated(a);

    resize_array<i32>(a, 0);

    // A tuple or record is allocated if any of its components are.
    var t: {i32[*], bool, i32};
    assert !allocated(t);

    resize_array<i32>(t.0, 10);
    t.1 = true;

    assert allocated(t);

    resize_array<i32>(t.0, 0);
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
// a more useful example of "allocated" in the next demo.


// Note: "allocated" cannot be used in executable code; it can only be used in
// verification contexts (asserts and preconditions and the like).


function main()
{
    fun2();
}


// To verify this example:
//   babylon -V Demo_11_Allocated.b

// To run this example:
//   babylon -c Demo_11_Allocated.b
//   gcc Demo_11_Allocated.c ExampleLib.c example_lib.c
//   ./a.out
