module Arrays
import Test;

interface {

// Array codegen tests

function f1(): u64
{
    var arr1: i32[];
    resize_array<i32>(arr1, 10);
    var result = sizeof(arr1);
    resize_array<i32>(arr1, 0);
    return result;
}

function f2(): u64
{
    var arr2: i32[,];
    resize_2d_array<i32>(arr2, 3, 4);
    var result = sizeof(arr2).0;
    resize_2d_array<i32>(arr2, 0, 0);
    return result;
}

function f3(): u64
{
    var arr2: i32[,];
    resize_2d_array<i32>(arr2, 3, 4);
    var result = sizeof(arr2).1;
    resize_2d_array<i32>(arr2, 0, 0);
    return result;
}


function sizeof_and_free<T>(ref a: T[]): u64
    requires !allocated(default<T>());
    requires forall (i:u64) i < sizeof(a) ==> !allocated(a[i]);
{
    var result = sizeof(a);
    resize_array<T>(a, 0);
    return result;
}

function f4(): u64
{
    var a: i32[];
    resize_array<i32>(a, 123);
    var result = sizeof_and_free<i32>(a);
    return result;
}

function f5(): u64
{
    var a: i32[,];
    resize_2d_array<i32>(a, 3, 2+3);
    var result = sizeof(a).0 * sizeof(a).1;
    resize_2d_array<i32>(a, 0, 0);
    return result;
}

function f6(): i32
{
    var a: i32[];
    resize_array<i32>(a, 10);
    var x: i32 = 0;

    var i = 0;
    while i < 10
        invariant sizeof(a) == u64(10);
        invariant 0 <= i <= 10;
        decreases ~i;
    {
        a[i] = i;
        i = i + 1;
    }
    
    x = a[3];

    resize_array<i32>(a, 0);
    return x;
}

function f8(): i32
{
    var a: {i32,i32}[];
    resize_array<{i32,i32}>(a, 10);
    
    var b: i32[];
    resize_array<i32>(b, 10);
    
    var x = 0;

    b[1] = 100;
    a[2].0 = b[1];
    a[2].1 = 20;     // a[2] = {100,20}
    a[3] = a[2];
    x = a[3].0 + a[3].1;    // x = 120

    resize_array<i32>(b, 0);
    resize_array<{i32,i32}>(a, 0);

    return x;
}

function f9(): u64
{
    // a "default" array isn't allocated and so doesn't need to be freed
    var a: i32[];
    var sz = sizeof(a);
    return sz;
}

function f10()
{
    var a: i32[,,];
    resize_3d_array<i32>(a, 5, 6, 7);
    a[4,5,6] = 4567;
    Test.print_i32(a[4,5,6]);
    resize_3d_array<i32>(a, 0, 0, 0);
}

function main()
{
    Test.print_u64(f1());
    Test.print_u64(f2());
    Test.print_u64(f3());
    Test.print_u64(f4());
    Test.print_u64(f5());
    Test.print_i32(f6());
    Test.print_i32(f8());
    Test.print_u64(f9());
    f10();
}

}
