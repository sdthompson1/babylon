// Memory allocation/freeing functions

module MemAlloc

import Int;    // built-in module (for now at least)
import IO;
import Maybe;

interface {

    // 'Mem' is used for the allocation functions because they are 
    // non-deterministic (from the point of view of the verifier) as
    // they might sometimes succeed and sometimes fail, even with
    // identical inputs.

    // (TODO: We could use the 'impure' keyword, then there would
    // be no need for this Mem type. But this example was written before
    // 'impure' was added to the language.)

    // Mem is marked 'allocated' just so that it can't be created
    // on the language side, and must be obtained from C.

    extern type Mem (allocated);


    ghost function default<T>(): T
    {
        var x: T;
        return x;
    }


    // Resize a 1-D array.
    extern function resize_array<T>(ref mem: Mem,
                                    ref array: T[*],
                                    new_size: u64): bool
                                   
        // This cannot be used to manufacture new allocated values.
        requires !allocated(default<T>());

        // Any elements being deleted must be non-allocated.
        requires forall (i: u64) new_size <= i < sizeof(array) ==> !allocated(array[i]);

        // If allocation fails, the array is unchanged.
        ensures !return ==> array == old(array);

        // If allocation succeeds, the size is changed.
        ensures return ==> sizeof(array) == new_size;

        // If allocation succeeds, any "existing" elements are unchanged.
        ensures return ==>
            forall (i: u64) i < old(sizeof(array)) && i < sizeof(array) ==>
                array[i] == old(array[i]);

        // If allocation succeeds, any "new" elements are equal to the default
        // for their type.
        ensures return ==>
            forall (i: u64) old(sizeof(array)) <= i < new_size ==>
                array[i] == default<T>();

        // Freeing will always succeed.
        ensures new_size == u64(0) ==> return;


    // Resize a 2-D array.
    extern function resize_2d_array<T>(ref mem: Mem,
                                       ref array: T[*,*],
                                       new_size_0: u64,
                                       new_size_1: u64): bool
                                      
        // The total number of elements must not overflow u64.
        requires Int.can_mul_u64(new_size_0, new_size_1);

        // This cannot be used to manufacture new allocated values.
        requires !allocated(default<T>());

        // Any elements being deleted must be non-allocated.
        requires forall (i: u64) forall (j: u64)
            i < sizeof(array).0 && j < sizeof(array).1 &&
            (i >= new_size_0 || i >= new_size_1) ==>
                !allocated(array[i, j]);

        // If allocation fails, the array is unchanged.
        ensures !return ==> array == old(array);

        // If allocation succeeds, the size is changed.
        ensures return ==> sizeof(array) == {new_size_0, new_size_1};

        // If allocation succeeds, any "existing" elements are unchanged.
        ensures return ==>
            forall (i: u64) forall (j: u64)
                i < new_size_0 && j < new_size_1 &&
                i < old(sizeof(array)).0 && j < old(sizeof(array)).1 ==>
                    array[i, j] == old(array[i, j]);

        // If allocation succeeds, any "new" elements are equal to the default
        // for their type.
        ensures return ==>
            forall (i: u64) forall (j: u64)
                i < new_size_0 && j < new_size_1 &&
                (i >= old(sizeof(array)).0 || j >= old(sizeof(array)).1) ==>
                    array[i, j] == default<T>();

        // Freeing will always succeed.
        ensures new_size_0 == u64(0) || new_size_1 == u64(0) ==> return;
}
