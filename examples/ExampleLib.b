
// The Babylon language doesn't currently come with any kind of
// "standard library". Indeed, there is no built-in way to even
// print out a string (or do any other kind of I/O) at the moment.

// We do, however, have a facility to "import" C functions into the
// program. Therefore, for now, in order to write real programs,
// one has to code the necessary I/O operations as C functions, and
// then import those functions into the Babylon program.

// This file (and its companion "example_lib.c") show an example
// of doing that. The C file defines "print_string" and "print_i32"
// for printing strings and numbers respectively. The code below
// imports these functions into a Babylon module called "ExampleLib".

// In addition, there are some array resizing functions (memory allocation
// and deallocation is another thing that is missing from the core language
// at the moment).

module ExampleLib

import Int;   // note: module "Int" is built in to the compiler, for now at least

interface
{
    // A "valid string" is a u8[] array containing a null byte somewhere
    // within it.
    ghost function valid_string(s: u8[]): bool
    {
        return exists (i: u64) i < sizeof(s) && s[i] == 0;
    }

    // Print a string to the terminal.
    extern function print_string(string: u8[])
        requires valid_string(string);

    // Prints an integer to the terminal.
    // Note this does not print a new line after the number; you
    // will need to explicitly call print_string("\n") if you want
    // that.
    extern function print_i32(x: i32);

    // More printing functions (for different types).
    extern function print_u32(x: u32);
    extern function print_i64(x: i64);
    extern function print_u64(x: u64);

    // Some useful constants.
    const I32_MIN: i32 = -2147483648;
    const I32_MAX: i32 = 2147483647;
    const U32_MAX: u32 = 4294967295;



    // Array resizing.

    // Note: These functions assume that memory allocation will always succeed
    // (the implementation actually aborts the program if malloc returns NULL).
    // In real programs, one might want more robust functions that can report
    // errors. The MemAlloc module in the Chess example shows one way of doing
    // that.

    extern function resize_array<T>(ref array: T[*], new_dim: u64)
    
        // This cannot be used to manufacture new allocated values.
        requires !allocated(default<T>());
        
        // Any elements being deleted must be non-allocated.
        requires forall (i: u64) new_dim <= i < sizeof(array) ==> !allocated(array[i]);

        // The array is resized to the new size.
        ensures sizeof(array) == new_dim;

        // The existing contents are preserved.
        ensures forall (i: u64) i < old(sizeof(array)) && i < new_dim ==> array[i] == old(array[i]);

        // The new elements are equal to the default for their type.
        ensures forall (i: u64) old(sizeof(array)) <= i < new_dim ==> array[i] == default<T>();


    extern function resize_2d_array<T>(ref array: T[*,*], dim0: u64, dim1: u64)

        // The total number of elements must not overflow u64.
        requires Int.can_mul_u64(dim0, dim1);

        // This cannot be used to manufacture new allocated values.
        requires !allocated(default<T>());

        // Any elements being deleted must be non-allocated.
        requires forall (i: u64) forall (j: u64)
            i < sizeof(array).0 && j < sizeof(array).1 &&
            (i >= dim0 || i >= dim1) ==>
                !allocated(array[i, j]);

        // The array is resized to the new size.
        ensures sizeof(array) == {dim0, dim1};

        // The existing contents are preserved.
        ensures forall (i: u64) forall (j: u64)
            i < old(sizeof(array)).0 && i < dim0 &&
            j < old(sizeof(array)).1 && j < dim1 ==>
                array[i, j] == old(array[i, j]);

        // The new elements are equal to the default for their type.
        ensures forall (i: u64) forall (j: u64)
            i < dim0 && j < dim1 &&
            (i >= old(sizeof(array)).0 || j >= old(sizeof(array)).1) ==>
                array[i, j] == default<T>();


    // This should really be built in to the language ... but for now, here
    // is a function that returns the default value of any given type.
    ghost function default<T>(): T
    {
        var x: T;
        return x;
    }
}
