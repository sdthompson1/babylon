// Support module for testcases.

module Test

interface
{
    const I32_MIN: i32 = -2147483648;
    const I32_MAX: i32 = 2147483647;
    const U64_MAX: u64 = 18446744073709551615;

    extern function print_i8 (x: i8);
    extern function print_i16(x: i16);
    extern function print_i32(x: i32);
    extern function print_i64(x: i64);

    extern function print_u8 (x: u8);
    extern function print_u16(x: u16);
    extern function print_u32(x: u32);
    extern function print_u64(x: u64);

    extern function print_bool(b: bool);

    ghost function valid_string(s: u8[]): bool
    {
        return exists (i: u64) i < sizeof(s) && s[i] == 0;
    }

    // Print a null-terminated string
    extern function print_string(s: u8[]);
        requires valid_string(s);

    ghost function default<T>(): T
    {
        var x: T;
        return x;
    }


    // For the purposes of the tests, memory allocation always
    // succeeds (the C implementation will abort the program
    // if we are out of memory). Therefore these "alloc_array"
    // functions always succeed, and don't need to be declared
    // "impure".
    
    extern function alloc_array<T>(ref array: T[*], dim: u64)
    
        // This cannot be used to manufacture new allocated values.
        requires !allocated(default<T>());
        
        // The array must be empty initially.
        requires sizeof(array) == u64(0);

        // The array is resized to the new size.
        ensures sizeof(array) == dim;

        // The new elements are equal to the default for their type.
        ensures forall (i: u64) i < dim ==> array[i] == default<T>();


    extern function free_array<T>(ref array: T[*])

        // Any elements being deleted must be non-allocated.
        requires forall (i: u64) i < sizeof(array) ==> !allocated(array[i]);

        // The array is resized to zero size.
        ensures sizeof(array) == u64(0);


    extern function alloc_2d_array<T>(ref array: T[*,*], dim0: u64, dim1: u64)

        // The total number of elements must not overflow u64.
        requires int(dim0) * int(dim1) <= int(U64_MAX);

        // This cannot be used to manufacture new allocated values.
        requires !allocated(default<T>());

        // The array must be empty initially.
        requires sizeof(array) == {u64(0), u64(0)};

        // The array is resized to the new size.
        ensures sizeof(array) == {dim0, dim1};

        // The new elements are equal to the default for their type.
        ensures forall (i: u64) forall (j: u64)
            i < dim0 && j < dim1 ==>
                array[i, j] == default<T>();

    extern function free_2d_array<T>(ref array: T[*,*])

        // Any elements being deleted must be non-allocated.
        requires forall (i: u64) forall (j: u64)
            i < sizeof(array).0 && j < sizeof(array).1 ==>
                !allocated(array[i, j]);

        // The array is resized to zero size.
        ensures sizeof(array) == {u64(0), u64(0)};


    extern function alloc_3d_array<T>(ref array: T[*,*,*], dim0: u64, dim1: u64, dim2: u64)

        // The total number of elements must not overflow u64.
        requires int(dim0) * int(dim1) * int(dim2) <= int(U64_MAX);

        // This cannot be used to manufacture new allocated values.
        requires !allocated(default<T>());

        // The array must be empty initially.
        requires sizeof(array) == {u64(0), u64(0), u64(0)};

        // The array is resized to the new size.
        ensures sizeof(array) == {dim0, dim1, dim2};

        // The new elements are equal to the default for their type.
        ensures forall (i: u64) forall (j: u64) forall (k: u64)
            i < dim0 && j < dim1 && k < dim2 ==>
                array[i, j, k] == default<T>();

    extern function free_3d_array<T>(ref array: T[*,*,*])

        // Any elements being deleted must be non-allocated.
        requires forall (i: u64) forall (j: u64) forall (k: u64)
            i < sizeof(array).0 && j < sizeof(array).1 && k < sizeof(array).2 ==>
                !allocated(array[i, j, k]);

        // The array is resized to zero size.
        ensures sizeof(array) == {u64(0), u64(0), u64(0)};



    // A sample allocated 'extern' type.
    extern type AllocTest (allocated);
    datatype MaybeAllocTest = MA_Nothing | MA_Just(AllocTest);
    
    extern function allocate_alloc_test(ref r: MaybeAllocTest)
        requires !allocated(r);
        ensures allocated(r);

    extern function free_alloc_test(ref r: MaybeAllocTest)
        requires allocated(r);
        ensures !allocated(r);
}
