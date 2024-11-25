// Example 5 -- Arrays.

// In this example we explain how arrays work in the Babylon language.

module Example05


interface {
    impure function main();
}


// Import the "Array" module which contains the "alloc_array" and
// "free_array" functions.
import Array;

import Console;


// Note: A function that allocates memory must be marked "impure".
// (TODO: write an example that explains "impure" in more detail.)
impure function fun1()
{
    // An array of fixed size can be created as follows:
    var fixed_size: i32[10];     // Array of 10 i32's.

    // A "resizable" array can be created by using the notation [*],
    // as follows:
    var a: i32[*];      // Resizable array of i32's.

    // The size (number of elements) of an array can be accessed by the
    // "sizeof" operator. In this case the array is empty (has size zero)
    // because resizable arrays always start out empty by default.
    assert sizeof(a) == 0;

    // Notes:
    // 1) The type returned by sizeof is always u64.
    // 2) sizeof is not to be confused with the sizeof operator in C
    // which returns the size in *bytes* of a value. In Babylon, sizeof
    // always returns the *number of elements* of an array.


    // To allocate (set the size) of a resizable array we can do
    // the following:
    var success = alloc_array(a, 100);

    // The alloc_array function needs to allocate memory from the operating
    // system. If memory was available it will return true, otherwise it
    // returns false.

    if success {

        // If alloc_array returned true, then it is guaranteed that the
        // array now has size 100. Therefore the following assert can be
        // proved:
        assert sizeof(a) == 100;


        // Before leaving the function, we must "free" the array, otherwise
        // there will be a memory leak. This can be done by calling
        // "free_array" as follows:
        free_array(a);


        // After freeing, the array has size zero again.
        assert sizeof(a) == 0;


        // In order to prevent memory leaks, the verifier checks that all arrays
        // have size zero before they go out of scope. Therefore, if the "free_array"
        // call (above) is removed, a verifier error will be observed.
        
    } else {
        // If memory allocation fails, the array will still have size zero:
        assert sizeof(a) == 0;

        // (Note that in this case, memory allocation is unlikely to fail because
        // the array is so small, but if very large arrays are being used, then
        // allocation failure is a distinct possibility.)
    }
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
    println("");

    // All array accesses are checked by the verifier to ensure that the
    // index value is within range. The following would produce a verifier
    // error (or in more detail: the SMT solver would be asked to prove
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

// Note: The i32[] notation cannot be used when declaring ordinary variables.
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
        
            count = count + 1;

        }
        idx = idx + 1;
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

    print("The number of zeroes in the array is ");
    print_u64(count_zeroes(a));  // prints 7
    println("");
}

impure function fun3()
{
    // It is possible to make an array of arrays. The trick is to first
    // allocate the base array, then individually allocate some (or all)
    // of the "inner" arrays.
    var a: i32[*][*];   // array of arrays of i32

    // Make 10 inner arrays
    var ok = alloc_array(a, 10);
    if ok {

        // Allocate some of the inner arrays
        ok = alloc_array(a[0], 5);
        ok = alloc_array(a[1], 6);
        ok = alloc_array(a[2], 4);

        // For the deallocation, the system won't allow us to deallocate "a" until
        // all of the inner arrays have size zero. So we first have to free each
        // inner array, then free the outer array.

        free_array(a[0]);
        free_array(a[1]);
        free_array(a[2]);
        free_array(a);
    }
}

impure function fun4()
{
    // It is also possible to have two-dimensional arrays.
    // Here is a fixed-size 2d array:
    var fixed_size: i32[10, 20];

    // And a resizable one:
    var a: i32[*, *];

    // Note you cannot mix fixed and variable sizes. E.g. the following
    // would be illegal:
    // var bad: i32[10, *];

    // The alloc_2d_array function be used for the allocation:
    var ok = alloc_2d_array(a, 10, 5);   // make a 10x5 array

    if ok {
        // For 2d arrays, sizeof returns a tuple of u64 values.
        // Tuples will be covered in a future demo, but for now, just be aware
        // that {x, y} is the notation for a pair (2-tuple) containing values
        // x and y.
        // (Also note that integer casting does not happen implicitly within a
        // tuple, so for the equality expression below to be well-typed, we must
        // explicitly state that "10" and "5" are u64 values.)
        assert sizeof(a) == {u64(10), u64(5)};

        // Elements can be accessed using the [] notation like this:
        a[2, 3] = 10;
        a[3, 4] = 20;
        print_i32(a[2, 3]);   // prints 10
        println("");

        // Once again, all accesses are checked to make sure they are in range,
        // so the following would fail:
        // a[20, 30] = 100;   // out of bounds
    }

    // 2d arrays can be freed using "free_2d_array".
    free_2d_array(a);
    assert sizeof(a) == {u64(0), u64(0)};


    // 3d and higher arrays (e.g. i32[*,*,*]) are also supported:
    var b: i32[*, *, *];

    // However, while "alloc_3d_array" is provided, there is no function for
    // "alloc_4d_array" or any higher dimension of array (as yet).
    // This could, however, be added to the Array module (in the coretypes
    // package) easily enough, if required.
}


impure function main()
{
    fun1();
    fun2();
    count_example();
    fun3();
}
