module Test
interface
{
    const I32_MIN: i32 = 0;
    const I32_MAX: i32 = 0;
    const U64_MAX: u64 = 0;
    extern function print_i8 (x: i8);
    extern function print_i16(x: i16);
    extern function print_i32(x: i32);
    extern function print_i64(x: i64);
    extern function print_u8 (x: u8);
    extern function print_u16(x: u16);
    extern function print_u32(x: u32);
    extern function print_u64(x: u64);
    extern function print_bool(b: bool);
    ghost function valid_string(s: u8[]): bool;
    extern function print_string(s: u8[]);
    ghost function default<T>(): T;
    extern function alloc_array<T>(ref array: T[*], dim: u64);
    extern function free_array<T>(ref array: T[*]);
    extern function alloc_2d_array<T>(ref array: T[*,*], dim0: u64, dim1: u64);
    extern function free_2d_array<T>(ref array: T[*,*]);
    extern function alloc_3d_array<T>(ref array: T[*,*,*], dim0: u64, dim1: u64, dim2: u64);
    extern function free_3d_array<T>(ref array: T[*,*,*]);
    extern type AllocTest (allocated_always);
    datatype MaybeAllocTest = MA_Nothing | MA_Just(AllocTest);    
    extern function allocate_alloc_test(ref r: MaybeAllocTest)
    extern function free_alloc_test(ref r: MaybeAllocTest)
}
