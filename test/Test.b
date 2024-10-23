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


    // Array allocation and freeing. We assume memory allocation always succeeds;
    // therefore these do not need to return "Maybe" and do not need to be marked "impure".

    extern function alloc_array<T: Move+Default>(dim: u64): T[*]
        ensures sizeof(return) == dim;
        ensures forall (i: u64) i < dim ==> return[i] == default<T>();

    extern function free_array<T: Move>(move array: T[*]);

    extern function alloc_2d_array<T: Move+Default>(dim0: u64, dim1: u64): T[*,*]
        requires can_mul_u64(dim0, dim1);
        ensures sizeof(return) == {dim0, dim1};
        ensures forall (i: u64) i < dim0 ==>
            forall (j: u64) j < dim1 ==> return[i, j] == default<T>();

    extern function free_2d_array<T: Move>(move array: T[*, *]);

    extern function alloc_3d_array<T: Move+Default>(dim0: u64, dim1: u64, dim2: u64): T[*,*,*]
        requires can_mul_u64(dim0, dim1);
        requires can_mul_u64(dim0 * dim1, dim2);
        ensures sizeof(return) == {dim0, dim1, dim2};
        ensures forall (i: u64) i < dim0 ==>
            forall (j: u64) j < dim1 ==>
               forall (k: u64) k < dim2 ==> return[i, j, k] == default<T>();

    extern function free_3d_array<T: Move>(move array: T[*, *, *]);
}
