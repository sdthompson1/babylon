module Array

import Default;
import Int;

interface {

    // ** Array allocation and freeing

    // This is 'impure' because the allocation might either succeed or fail,
    // in a non-deterministic way.
    extern impure function alloc_array<T> (ref arr: T[*], size: u64): bool
        requires sizeof(arr) == 0;
        requires size != 0;
        ensures return ==> sizeof(arr) == size;
        ensures return ==> forall (i: u64) i < size ==> arr[i] == default<T>();
        ensures !return ==> arr == old(arr);

    // Freeing always succeeds, so free_array does not need to be 'impure'.
    extern function free_array<T> (ref arr: T[*])
        ensures sizeof(arr) == 0;

    extern impure function alloc_2d_array<T> (ref arr: T[*,*], size0: u64, size1: u64): bool
        requires !allocated(arr);
        requires int(0) < int(size0) * int(size1) <= int(U64_MAX);
        ensures return ==> sizeof(arr) == {size0, size1};
        ensures return ==>
            forall (i: u64) i < size0 ==>
                forall (j: u64) j < size1 ==>
                    arr[i, j] == default<T>();
        ensures !return ==> arr == old(arr);

    extern function free_2d_array<T> (ref arr: T[*,*])
        ensures sizeof(arr) == {u64(0), u64(0)};

    extern impure function alloc_3d_array<T> (ref arr: T[*,*,*], size0: u64, size1: u64, size2: u64): bool
        requires !allocated(arr);
        requires int(0) < int(size0) * int(size1) * int(size2) <= int(U64_MAX);
        ensures return ==> sizeof(arr) == {size0, size1, size2};
        ensures return ==>
            forall (i: u64) i < size0 ==>
                forall (j: u64) j < size1 ==>
                    forall (k: u64) k < size2 ==>
                        arr[i, j, k] == default<T>();
        ensures !return ==> arr == old(arr);

    extern function free_3d_array<T>(ref arr: T[*,*,*])
        ensures sizeof(arr) == {u64(0), u64(0), u64(0)};


    // ** Ghost array allocation

    ghost function alloc_ghost_array<T> (ref arr: T[*], size: u64)
        ensures sizeof(arr) == size;
        ensures forall (i: u64) i < size ==> arr[i] == default<T>();

    ghost function alloc_ghost_2d_array<T> (ref arr: T[*,*], size0: u64, size1: u64)
        ensures sizeof(arr) == {size0, size1};
        ensures forall (i: u64) i < size0 ==>
            forall (j: u64) j < size1 ==>
                arr[i, j] == default<T>();

    ghost function alloc_ghost_3d_array<T> (ref arr: T[*,*,*], size0: u64, size1: u64, size2: u64)
        ensures sizeof(arr) == {size0, size1, size2};
        ensures forall (i: u64) i < size0 ==>
            forall (j: u64) j < size1 ==>
                forall (k: u64) k < size2 ==>
                    arr[i, j, k] == default<T>();


    // ** Array copying

    // Copy the whole array 'src' to 'dest'.
    function copy_array<T> (ref dest: T[], src: T[])
        requires sizeof(dest) == sizeof(src);
        requires forall (i: u64) i < sizeof(src) ==> !allocated(src[i]);
        requires forall (i: u64) i < sizeof(dest) ==> !allocated(dest[i]);
        ensures dest == src;

    // Copy 'num_elems' from src, beginning at position 'src_idx', to
    // positions 'dest_idx' onwards in 'dest'. The src and dest arrays
    // must be different.
    function copy_array_section<T> (ref dest: T[], dest_idx: u64,
                                    src: T[], src_idx: u64, num_elems: u64)
        requires int(src_idx) + int(num_elems) <= int(sizeof(src));
        requires int(dest_idx) + int(num_elems) <= int(sizeof(dest));
        requires forall (i: u64) i < num_elems ==> !allocated(src[src_idx + i]);
        requires forall (i: u64) i < num_elems ==> !allocated(dest[dest_idx + i]);
        ensures sizeof(dest) == old(sizeof(dest));  // TODO: the compiler should know this already, without me having to say.
        ensures forall (i: u64) i < num_elems ==>
            dest[dest_idx + i] == src[src_idx + i];
        ensures forall (i: u64) i < dest_idx || dest_idx + num_elems <= i < sizeof(dest) ==>
            dest[i] == old(dest[i]);

    // Copy 'num_elems' starting from position 'src_idx' to the same
    // sized range starting from 'dest_idx', in the same array. The
    // two ranges may overlap.
    function move_array_section<T> (ref arr: T[], dest_idx: u64, src_idx: u64, num_elems: u64)
        requires int(src_idx) + int(num_elems) <= int(sizeof(arr));
        requires int(dest_idx) + int(num_elems) <= int(sizeof(arr));
        requires forall (i: u64) i < num_elems ==> !allocated(arr[src_idx + i]);
        requires forall (i: u64) i < num_elems ==> !allocated(arr[dest_idx + i]);
        ensures sizeof(arr) == old(sizeof(arr));
        ensures forall (i: u64) i < num_elems ==>
            arr[dest_idx + i] == old(arr)[src_idx + i];
        ensures forall (i: u64) i < dest_idx || dest_idx + num_elems <= i < sizeof(arr) ==>
            arr[i] == old(arr[i]);

    function copy_2d_array<T> (ref dest: T[,], src: T[,])
        requires sizeof(dest) == sizeof(src);
        requires forall (i: u64) i < sizeof(src).0 ==>
            forall (j: u64) j < sizeof(src).1 ==>
                !allocated(src[i, j]);
        requires forall (i: u64) i < sizeof(dest).0 ==>
            forall (j: u64) j < sizeof(dest).1 ==>
                !allocated(dest[i, j]);
        ensures dest == src;

    function copy_3d_array<T> (ref dest: T[,,], src: T[,,])
        requires sizeof(dest) == sizeof(src);
        requires forall (i: u64) i < sizeof(src).0 ==>
            forall (j: u64) j < sizeof(src).1 ==>
                forall (k: u64) k < sizeof(src).2 ==>
                    !allocated(src[i, j, k]);
        requires forall (i: u64) i < sizeof(dest).0 ==>
            forall (j: u64) j < sizeof(dest).1 ==>
                forall (k: u64) k < sizeof(src).2 ==>
                    !allocated(dest[i, j, k]);
        ensures dest == src;


    // ** Array filling

    function fill_array<T> (ref arr: T[], value: T)
        requires !allocated(value);
        requires forall (i: u64) i < sizeof(arr) ==> !allocated(arr[i]);
        ensures sizeof(arr) == old(sizeof(arr));
        ensures forall (i: u64) i < sizeof(arr) ==> arr[i] == value;

    function fill_array_section<T> (ref arr: T[], idx: u64, num_elems: u64, value: T)
        requires int(idx) + int(num_elems) <= int(sizeof(arr));
        requires !allocated(value);
        requires forall (i: u64) i < num_elems ==> !allocated(arr[idx + i]);
        ensures sizeof(arr) == old(sizeof(arr));
        ensures forall (i: u64) i < num_elems ==> arr[idx + i] == value;
        ensures forall (i: u64) i < idx || idx + num_elems <= i < sizeof(arr) ==> arr[i] == old(arr[i]);

    function fill_2d_array<T> (ref arr: T[,], value: T)
        requires !allocated(value);
        requires forall (i: u64) i < sizeof(arr).0 ==>
            forall (j: u64) j < sizeof(arr).1 ==>
                !allocated(arr[i, j]);
        ensures sizeof(arr) == old(sizeof(arr));
        ensures forall (i: u64) i < sizeof(arr).0 ==>
            forall (j: u64) j < sizeof(arr).1 ==>
                arr[i, j] == value;

    function fill_3d_array<T> (ref arr: T[,,], value: T)
        requires !allocated(value);
        requires forall (i: u64) i < sizeof(arr).0 ==>
            forall (j: u64) j < sizeof(arr).1 ==>
                forall (k: u64) k < sizeof(arr).2 ==>
                    !allocated(arr[i, j, k]);
        ensures sizeof(arr) == old(sizeof(arr));
        ensures forall (i: u64) i < sizeof(arr).0 ==>
            forall (j: u64) j < sizeof(arr).1 ==>
                forall (k: u64) k < sizeof(arr).2 ==>
                    arr[i, j, k] == value;
}

ghost function alloc_ghost_array<T> (ref arr: T[*], size: u64)
    ensures sizeof(arr) == size;
    ensures forall (i: u64) i < size ==> arr[i] == default<T>();
{
    // For now, this isn't proved; we just take it as axiomatic that there
    // exists an array, of the given size, with all elements equal to
    // default<T>().
    assume false;
}

ghost function alloc_ghost_2d_array<T> (ref arr: T[*,*], size0: u64, size1: u64)
    ensures sizeof(arr) == {size0, size1};
    ensures forall (i: u64) i < size0 ==>
        forall (j: u64) j < size1 ==>
            arr[i, j] == default<T>();
{
    assume false;
}

ghost function alloc_ghost_3d_array<T> (ref arr: T[*,*,*], size0: u64, size1: u64, size2: u64)
    ensures sizeof(arr) == {size0, size1, size2};
    ensures forall (i: u64) i < size0 ==>
        forall (j: u64) j < size1 ==>
            forall (k: u64) k < size2 ==>
                arr[i, j, k] == default<T>();
{
    assume false;
}

function copy_array<T> (ref dest: T[], src: T[])
    requires sizeof(dest) == sizeof(src);
    requires forall (i: u64) i < sizeof(src) ==> !allocated(src[i]);
    requires forall (i: u64) i < sizeof(dest) ==> !allocated(dest[i]);
    ensures dest == src;
{
    var size: u64 = sizeof(dest);
    var i: u64 = 0;
    
    while i < size
        invariant i <= sizeof(dest) == size;
        invariant forall (j: u64) j < sizeof(dest) ==> !allocated(dest[j]);
        invariant forall (j: u64) j < i ==> dest[j] == src[j];
        decreases ~i;
    {
        dest[i] = src[i];
        i = i + 1;
    }
}

function copy_array_section<T> (ref dest: T[], dest_idx: u64,
                                src: T[], src_idx: u64, num_elems: u64)
    requires int(src_idx) + int(num_elems) <= int(sizeof(src));
    requires int(dest_idx) + int(num_elems) <= int(sizeof(dest));
    requires forall (i: u64) i < num_elems ==> !allocated(src[src_idx + i]);
    requires forall (i: u64) i < num_elems ==> !allocated(dest[dest_idx + i]);
    ensures sizeof(dest) == old(sizeof(dest));  // TODO: the compiler should know this already, without me having to say.
    ensures forall (i: u64) i < num_elems ==>
        dest[dest_idx + i] == src[src_idx + i];
    ensures forall (i: u64) i < dest_idx || dest_idx + num_elems <= i < sizeof(dest) ==>
        dest[i] == old(dest[i]);
{
    ghost var old_dest = dest;

    var i: u64 = 0;
    while i < num_elems
        invariant i <= num_elems <= sizeof(dest) == sizeof(old_dest);
        invariant forall (j: u64) j < i ==> dest[dest_idx + j] == src[src_idx + j];
        invariant forall (j: u64) j < dest_idx || dest_idx + i <= j < sizeof(dest) ==>
            dest[j] == old_dest[j];
        decreases ~i;
    {
        dest[dest_idx + i] = src[src_idx + i];
        i = i + 1;
    }
}

function move_array_section<T> (ref arr: T[], dest_idx: u64, src_idx: u64, num_elems: u64)
    requires int(src_idx) + int(num_elems) <= int(sizeof(arr));
    requires int(dest_idx) + int(num_elems) <= int(sizeof(arr));
    requires forall (i: u64) i < num_elems ==> !allocated(arr[src_idx + i]);
    requires forall (i: u64) i < num_elems ==> !allocated(arr[dest_idx + i]);
    ensures sizeof(arr) == old(sizeof(arr));
    ensures forall (i: u64) i < num_elems ==>
        arr[dest_idx + i] == old(arr)[src_idx + i];
    ensures forall (i: u64) i < dest_idx || dest_idx + num_elems <= i < sizeof(arr) ==>
        arr[i] == old(arr[i]);
{
    ghost var old_arr = arr;
    
    if dest_idx > src_idx {
        // Copy downwards
        var i: u64 = num_elems;
        while i > 0
            invariant i <= num_elems <= sizeof(arr) == sizeof(old_arr);
            invariant forall (j: u64) i <= j < num_elems ==> arr[dest_idx + j] == old_arr[src_idx + j];
            invariant forall (j: u64) j < dest_idx + i || dest_idx + num_elems <= j < sizeof(arr) ==>
                arr[j] == old_arr[j];
            decreases i;
        {
            i = i - 1;
            arr[dest_idx + i] = arr[src_idx + i];
        }
    } else {
        // Copy upwards
        var i: u64 = 0;
        while i < num_elems
            invariant i <= num_elems <= sizeof(arr) == sizeof(old_arr);
            invariant forall (j: u64) j < i ==> arr[dest_idx + j] == old_arr[src_idx + j];
            invariant forall (j: u64) j < dest_idx || dest_idx + i <= j < sizeof(arr) ==>
                arr[j] == old_arr[j];
            decreases ~i;
        {
            arr[dest_idx + i] = arr[src_idx + i];
            i = i + 1;
        }
    }
}

function copy_2d_array<T> (ref dest: T[,], src: T[,])
    requires sizeof(dest) == sizeof(src);
    requires forall (i: u64) i < sizeof(src).0 ==>
        forall (j: u64) j < sizeof(src).1 ==>
            !allocated(src[i, j]);
    requires forall (i: u64) i < sizeof(dest).0 ==>
        forall (j: u64) j < sizeof(dest).1 ==>
            !allocated(dest[i, j]);
    ensures dest == src;
{
    var size: {u64, u64} = sizeof(dest);

    var j: u64 = 0;
    while j < size.1
        invariant sizeof(dest) == size;
        invariant j <= size.1;
        invariant forall (ii: u64) forall (jj: u64)
            ii < size.0 && jj < j ==> dest[ii, jj] == src[ii, jj];
        invariant forall (ii: u64) forall (jj: u64)
            ii < size.0 && jj < size.1 ==> !allocated(dest[ii, jj]);
        decreases ~j;
    {
        var i: u64 = 0;
        while i < size.0
            invariant sizeof(dest) == size;
            invariant i <= size.0;
            invariant forall (ii: u64) forall (jj: u64)
                ii < size.0 && jj < size.1 && (jj < j || jj == j && ii < i) ==>
                    dest[ii, jj] == src[ii, jj];
            invariant forall (ii: u64) forall (jj: u64)
                ii < size.0 && jj < size.1 ==> !allocated(dest[ii, jj]);
            decreases ~i;
        {
            dest[i, j] = src[i, j];
            i = i + 1;
        }
        j = j + 1;
    }
}

function copy_3d_array<T> (ref dest: T[,,], src: T[,,])
    requires sizeof(dest) == sizeof(src);
    requires forall (i: u64) i < sizeof(src).0 ==>
        forall (j: u64) j < sizeof(src).1 ==>
            forall (k: u64) k < sizeof(src).2 ==>
                !allocated(src[i, j, k]);
    requires forall (i: u64) i < sizeof(dest).0 ==>
        forall (j: u64) j < sizeof(dest).1 ==>
            forall (k: u64) k < sizeof(src).2 ==>
                !allocated(dest[i, j, k]);
    ensures dest == src;
{
    var size: {u64, u64, u64} = sizeof(dest);

    var k: u64 = 0;
    while k < size.2
        invariant sizeof(dest) == size;
        invariant k <= size.2;
        invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
            ii < size.0 && jj < size.1 && kk < k ==> dest[ii, jj, kk] == src[ii, jj, kk];
        invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
            ii < size.0 && jj < size.1 && kk < size.2 ==> !allocated(dest[ii, jj, kk]);
        decreases ~k;
    {
        var j: u64 = 0;
        while j < size.1
            invariant sizeof(dest) == size;
            invariant j <= size.1;
            invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
                ii < size.0 && jj < size.1 && kk < size.2
                && (kk < k || kk == k && jj < j) ==>
                    dest[ii, jj, kk] == src[ii, jj, kk];
            invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
                ii < size.0 && jj < size.1 && kk < size.2 ==> !allocated(dest[ii, jj, kk]);
            decreases ~j;
        {
            var i: u64 = 0;
            while i < size.0
                invariant sizeof(dest) == size;
                invariant i <= size.0;
                invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
                    ii < size.0 && jj < size.1 && kk < size.2
                    && (kk < k || kk == k && (jj < j || jj == j && ii < i)) ==>
                        dest[ii, jj, kk] == src[ii, jj, kk];
                invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
                    ii < size.0 && jj < size.1 && kk < size.2 ==> !allocated(dest[ii, jj, kk]);
                decreases ~i;
            {
                dest[i, j, k] = src[i, j, k];
                i = i + 1;
            }
            j = j + 1;
        }
        k = k + 1;
    }
}

function fill_array<T> (ref arr: T[], value: T)
    requires !allocated(value);
    requires forall (i: u64) i < sizeof(arr) ==> !allocated(arr[i]);
    ensures sizeof(arr) == old(sizeof(arr));
    ensures forall (i: u64) i < sizeof(arr) ==> arr[i] == value;
{
    var size: u64 = sizeof(arr);
    var i: u64 = 0;

    while i < size
        invariant i <= sizeof(arr) == size;
        invariant forall (j: u64) j < sizeof(arr) ==> !allocated(arr[j]);
        invariant forall (j: u64) j < i ==> arr[j] == value;
        decreases ~i;
    {
        arr[i] = value;
        i = i + 1;
    }
}

function fill_array_section<T> (ref arr: T[], idx: u64, num_elems: u64, value: T)
    requires int(idx) + int(num_elems) <= int(sizeof(arr));
    requires !allocated(value);
    requires forall (i: u64) i < num_elems ==> !allocated(arr[idx + i]);
    ensures sizeof(arr) == old(sizeof(arr));
    ensures forall (i: u64) i < num_elems ==> arr[idx + i] == value;
    ensures forall (i: u64) i < idx || idx + num_elems <= i < sizeof(arr) ==> arr[i] == old(arr[i]);
{
    ghost var old_arr = arr;

    var i: u64 = 0;
    while i < num_elems
        invariant i <= num_elems <= sizeof(arr) == sizeof(old_arr);
        invariant forall (j: u64) j < i ==> arr[idx + j] == value;
        invariant forall (j: u64) j < idx || idx + i <= j < sizeof(arr) ==> arr[j] == old_arr[j];
        decreases ~i;
    {
        arr[idx + i] = value;
        i = i + 1;
    }
}

function fill_2d_array<T> (ref arr: T[,], value: T)
    requires !allocated(value);
    requires forall (i: u64) i < sizeof(arr).0 ==>
        forall (j: u64) j < sizeof(arr).1 ==>
            !allocated(arr[i, j]);
    ensures sizeof(arr) == old(sizeof(arr));
    ensures forall (i: u64) i < sizeof(arr).0 ==>
        forall (j: u64) j < sizeof(arr).1 ==>
            arr[i, j] == value;
{
    var size: {u64, u64} = sizeof(arr);

    var j: u64 = 0;
    while j < size.1
        invariant sizeof(arr) == size;
        invariant j <= size.1;
        invariant forall (ii: u64) forall (jj: u64)
            ii < size.0 && jj < j ==> arr[ii, jj] == value;
        invariant forall (ii: u64) forall (jj: u64)
            ii < size.0 && jj < size.1 ==> !allocated(arr[ii, jj]);
        decreases ~j;
    {
        var i: u64 = 0;
        while i < size.0
            invariant sizeof(arr) == size;
            invariant i <= size.0;
            invariant forall (ii: u64) forall (jj: u64)
                ii < size.0 && jj < size.1 && (jj < j || jj == j && ii < i) ==>
                    arr[ii, jj] == value;
            invariant forall (ii: u64) forall (jj: u64)
                ii < size.0 && jj < size.1 ==> !allocated(arr[ii, jj]);
            decreases ~i;
        {
            arr[i, j] = value;
            i = i + 1;
        }
        j = j + 1;
    }
}

function fill_3d_array<T> (ref arr: T[,,], value: T)
    requires !allocated(value);
    requires forall (i: u64) i < sizeof(arr).0 ==>
        forall (j: u64) j < sizeof(arr).1 ==>
            forall (k: u64) k < sizeof(arr).2 ==>
                !allocated(arr[i, j, k]);
    ensures sizeof(arr) == old(sizeof(arr));
    ensures forall (i: u64) i < sizeof(arr).0 ==>
        forall (j: u64) j < sizeof(arr).1 ==>
            forall (k: u64) k < sizeof(arr).2 ==>
                arr[i, j, k] == value;
{
    var size: {u64, u64, u64} = sizeof(arr);

    var k: u64 = 0;
    while k < size.2
        invariant sizeof(arr) == size;
        invariant k <= size.2;
        invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
            ii < size.0 && jj < size.1 && kk < k ==> arr[ii, jj, kk] == value;
        invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
            ii < size.0 && jj < size.1 && kk < size.2 ==> !allocated(arr[ii, jj, kk]);
        decreases ~k;
    {
        var j: u64 = 0;
        while j < size.1
            invariant sizeof(arr) == size;
            invariant j <= size.1;
            invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
                ii < size.0 && jj < size.1 && kk < size.2
                && (kk < k || kk == k && jj < j) ==>
                    arr[ii, jj, kk] == value;
            invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
                ii < size.0 && jj < size.1 && kk < size.2 ==> !allocated(arr[ii, jj, kk]);
            decreases ~j;
        {
            var i: u64 = 0;
            while i < size.0
                invariant sizeof(arr) == size;
                invariant i <= size.0;
                invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
                    ii < size.0 && jj < size.1 && kk < size.2
                    && (kk < k || kk == k && (jj < j || jj == j && ii < i)) ==>
                        arr[ii, jj, kk] == value;
                invariant forall (ii: u64) forall (jj: u64) forall (kk: u64)
                    ii < size.0 && jj < size.1 && kk < size.2 ==> !allocated(arr[ii, jj, kk]);
                decreases ~i;
            {
                arr[i, j, k] = value;
                i = i + 1;
            }
            j = j + 1;
        }
        k = k + 1;
    }
}
