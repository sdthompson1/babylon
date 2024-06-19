
// This is the fifth demonstration program for the Babylon language.

// In this demo we will explain how arrays work in this language.

module Demo_05_Arrays

interface {
    function main();
}

import ExampleLib;


function fun1()
{
    // An array of fixed size can be created as follows:
    var fixed_size: i32[10];     // Array of 10 i32's

    // A "resizable" array can be created by using the notation [*],
    // as follows:
    var a: i32[*];      // Resizable array of i32's.

    // The size (number of elements) of an array can be accessed by the
    // "sizeof" operator. In this case the array is empty (has size zero)
    // because resizable arrays always start out empty by default.
    assert sizeof(a) == u64(0);


    // Note: sizeof returns a u64. This is why we have to write u64(0)
    // instead of just 0 in the above (see also Demo_04_Casts.b).
    

    // The language doesn't currently have a built-in way to resize
    // an array. Instead we must call the function resize_array from the
    // ExampleLib. This is done as follows:
    resize_array(a, 100);

    // The array a now has size 100:
    assert sizeof(a) == u64(100);


    // The resize_array function allocates more memory from the operating
    // system (using malloc or a related function). We must free this memory
    // before the array "a" goes out of scope. This is done by resizing
    // the array back to zero size again:
    resize_array(a, 0);


    // The verifier checks that all arrays have size zero before they go
    // out of scope (this is to prevent memory leaks). Therefore, if the
    // previous line is removed, a verifier error will be observed.
}


function fun2()
{
    // Here we show how to access array elements.
    var a: i32[10];

    // Elements can be accessed using the [ ] operator (similar to C).
    // The array elements are numbered starting from zero, and going up
    // to the size of the array minus one.
    a[0] = 1;    // set first array element to 1
    a[9] = 2;    // set last array element to 2
    print_i32(a[0] + a[1] + a[9]);   // prints 3
    print_string("\n");

    // All array accesses are checked by the verifier to ensure that the
    // index value is within range. The following would produce a verifier
    // error (more specifically, the SMT solver would be asked to prove
    // that the index, 10, is less than the size of the array, which is
    // also 10; so this would fail).
    // a[10] = 3;  // try to access element outside bounds of array
}


// Arrays can be passed to functions. This does NOT make a copy of the entire
// array -- instead it just passes a pointer and a size value.
// Therefore arrays can be passed to functions without fear of inefficiency,
// even if the array is large.


// Here we show an example that counts how many zero values are in an array.

// Note: The "a" parameter, below, is declared to have type i32[], which
// means that it can either be a resizable array (i32[*]) or an array of
// some fixed size (i32[n], for some n) -- the function does not care.
// (We could also have declared "a" as, for example., "a: i32[10]" if we
// wanted a particular size of array, or "a: i32[*]" if we wanted specifically
// a resizable array, for whatever reason.)

// Note 2: The i32[] notation cannot be used when declaring ordinary variables.
// It can only be used in function arguments.

function count_zeroes(a: i32[]): u64
{
    var count: u64 = 0;
    var idx: u64 = 0;
    
    while idx < sizeof(a)
    
        // This invariant is necessary, otherwise "count + 1" might overflow.
        invariant count <= idx;
        
        decreases ~idx;
    {
        // Here we know that idx < sizeof(a) (because of the while-condition)
        // and therefore this index is within bounds.
        if a[idx] == 0 {
        
            count = count + u64(1);

        }
        idx = idx + u64(1);
    }
    return count;
}


// A simple example to demonstrate count_zeroes.
function count_example()
{
    var a: i32[10];
    a[0] = 1;
    a[1] = 2;
    a[2] = 3;
    // Note: all other array elements (3 to 9 inclusive) are equal to their
    // default value (zero in this case), so currently there are 7 zero
    // elements.

    print_string("The number of zeroes in the array is ");
    print_u64(count_zeroes(a));  // prints 7
    print_string("\n");
}

function fun3()
{
    // It is possible to make an array of arrays. The trick is to first
    // resize the base array, then individually resize some of the "inner"
    // arrays.
    var a: i32[*][*];   // array of arrays of i32

    resize_array(a, 10);   // make 10 inner arrays

    resize_array(a[0], 5);   // allocate some of the inner arrays
    resize_array(a[1], 6);
    resize_array(a[2], 4);

    // For the deallocation, the system won't allow us to deallocate "a" until
    // all of the inner arrays have size zero. So we first have to free each
    // inner array, then free the outer array.

    resize_array(a[0], 0);
    resize_array(a[1], 0);
    resize_array(a[2], 0);
    resize_array(a, 0);
}

function fun4()
{
    // It is also possible to have two-dimensional arrays.
    // Here is a fixed-size 2d array:
    var fixed_size: i32[10, 20];

    // And a resizable one:
    var a: i32[*, *];

    // Note you cannot mix fixed and variable sizes. E.g. the following
    // would be illegal:
    // var bad: i32[10, *];

    // The resize_2d_array function from ExampleLib can be used for the
    // allocation:
    resize_2d_array(a, 10, 5);   // make a 10x5 array

    // For 2d arrays, sizeof returns a tuple of u64 values.
    // Tuples will be covered in a future demo, but for now, be advised
    // that {x, y} is the notation for a pair (2-tuple) containing values
    // x and y.
    assert sizeof(a) == {u64(10), u64(5)};

    // Elements can be accessed using the [] notation like this:
    a[2, 3] = 10;
    a[3, 4] = 20;
    print_i32(a[2, 3]);   // prints 10
    print_string("\n");

    // Once again, all accesses are checked to make sure they are in range,
    // so the following would fail:
    // a[20, 30] = 100;   // out of bounds

    // To free a 2d array we resize it to size 0, 0.
    resize_2d_array(a, 0, 0);
    assert sizeof(a) == {u64(0), u64(0)};


    // Theoretically, 3d and higher arrays (e.g. i32[*,*,*]) are also supported:
    var b: i32[*, *, *];

    // However, the ExampleLib doesn't currently contain a function to
    // resize a 3d array. If 3d arrays were wanted, either such a function
    // would have to be written in C (and added to the ExampleLib), or,
    // a fixed-size 3d array could be used instead.
}


function main()
{
    fun1();
    fun2();
    count_example();
    fun3();
}


// To verify this example:
//   babylon -V Demo_05_Arrays.b

// To run this example:
//   babylon -c Demo_05_Arrays.b
//   gcc Demo_05_Arrays.c ExampleLib.c example_lib.c
//   ./a.out
