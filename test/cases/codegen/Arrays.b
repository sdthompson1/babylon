module Arrays
import Test;

interface {

// Array codegen tests

function f1(): u64
{
    var arr1: i32[*] = alloc_array(10);
    var result = sizeof(arr1);
    free_array(arr1);
    return result;
}

function f2(): u64
{
    var arr2: i32[*,*] = alloc_2d_array(3, 4);
    var result = sizeof(arr2).0;
    free_2d_array(arr2);
    return result;
}

function f3(): u64
{
    var arr2: i32[*,*] = alloc_2d_array(3, 4);
    var result = sizeof(arr2).1;
    free_2d_array(arr2);
    return result;
}


function sizeof_and_free<T: Move>(move a: T[*]): u64
{
    var result = sizeof(a);
    free_array(a);
    return result;
}

function f4(): u64
{
    var a: i32[*] = alloc_array(123);
    var result = sizeof_and_free(a);
    return result;
}

function f5(): u64
{
    var a: i32[*,*] = alloc_2d_array<i32>(3, 2+3);
    var result = sizeof(a).0 * sizeof(a).1;
    free_2d_array<i32>(a);
    return result;
}

function f6(): i32
{
    var a: i32[*] = alloc_array(10);
    var x: i32 = 0;

    var i = 0;
    while i < 10
        invariant sizeof(a) == 10;
        invariant 0 <= i <= 10;
        decreases ~i;
    {
        a[i] = i;
        i = i + 1;
    }
    
    x = a[3];

    free_array(a);
    return x;
}

function f8(): i32
{
    var a: {i32,i32}[*] = alloc_array(10);    
    var b: i32[*] = alloc_array(10);
    
    var x = 0;

    b[1] = 100;
    a[2].0 = b[1];
    a[2].1 = 20;     // a[2] = {100,20}
    a[3] = a[2];
    x = a[3].0 + a[3].1;    // x = 120

    free_array(b);
    free_array(a);

    return x;
}

function f9(): u64
{
    // a "default" array has size 0 - but still needs to be freed
    var a: i32[*];
    var sz = sizeof(a);
    free_array(a);
    return sz;
}

function f10()
{
    var a: i32[*,*,*] = alloc_3d_array(5, 6, 7);
    a[4,5,6] = 4567;
    Test.print_i32(a[4,5,6]);
    free_3d_array(a);
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
