// Support module for testcases.

module Test

import Int;

interface
{
    // Note: These functions are defined in test_support.c.
    
    extern function print_i8 (x: i8);
    extern function print_i16(x: i16);
    extern function print_i32(x: i32);
    extern function print_i64(x: i64);

    extern function print_u8 (x: u8);
    extern function print_u16(x: u16);
    extern function print_u32(x: u32);
    extern function print_u64(x: u64);

    extern function print_bool(b: bool);

    extern function print_string(s: u8[]);


    ghost function default<T>(): T
    {
        var x: T;
        return x;
    }


    // For the purposes of the tests, memory allocation always
    // succeeds (the C implementation will abort the program
    // if we are out of memory). Therefore these "resize"
    // functions always succeed, and don't need a separate
    // dummy argument to ensure purity.
    
    extern function resize_array<T>(ref array: T[], new_dim: u64)
    
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


    extern function resize_2d_array<T>(ref array: T[,], dim0: u64, dim1: u64)

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


    extern function resize_3d_array<T>(ref array: T[,,], dim0: u64, dim1: u64, dim2: u64)

        // The total number of elements must not overflow u64.
        requires Int.can_mul_u64(dim0, dim1);
        requires Int.can_mul_u64(dim0 * dim1, dim2);

        // For simplicity -- this can only be used with non-allocated types.
        requires forall (x: T) !allocated(x);

        // The array is resized to the new size.
        ensures sizeof(array) == {dim0, dim1, dim2};

        // For simplicity -- all elements are reset to default.
        ensures forall (i: u64) forall (j: u64) forall (k: u64)
            i < dim0 && j < dim1 && k < dim2 ==>
                array[i, j, k] == default<T>();



    // A sample allocated abstract type.
    type AllocTest (allocated);
    datatype MaybeAllocTest = MA_Nothing | MA_Just(AllocTest);
    
    extern function allocate_alloc_test(ref r: MaybeAllocTest)
        requires !allocated(r);
        ensures allocated(r);

    extern function free_alloc_test(ref r: MaybeAllocTest)
        requires allocated(r);
        ensures !allocated(r);
}
