module Arrays3

interface {
    function main();
}

import Test;

function f1(ref a: i32[,])
    requires sizeof(a).0 >= u64(10);
    requires sizeof(a).1 >= u64(8);
{
    a[0,0] = 1000;
    a[9,7] = 2000;
}

function f2(ref a: i32[10,20])
{
    a[0,0] = 1000;
    a[9,7] = 2000;
}

function test1()
{
    var a: i32[20,20];
    a[3,3] = 3333;

    f1(a);

    print_i32(a[0,0]);
    print_i32(a[9,7]);
    print_i32(a[3,3]);
    print_i32(a[1,1]);
}

function test2()
{
    var a: i32[*,*] = alloc_2d_array(10, 8);

    a[3,3] = 3333;

    f1(a);

    print_i32(a[0,0]);
    print_i32(a[9,7]);
    print_i32(a[3,3]);
    print_i32(a[1,1]);

    free_2d_array(a);
}

function test3()
{
    var a: i32[*,*] = alloc_2d_array(10, 20);

    a[3,3] = 3333;

    f2(a);
    
    print_i32(a[0,0]);
    print_i32(a[9,7]);
    print_i32(a[3,3]);
    print_i32(a[1,1]);

    free_2d_array<i32>(a);
}

function fn4(move r: i8[*]): i8[*]
    requires sizeof(r) == u64(10);
{
    return r;
}

function test4()
{
    var x: i8[*] = alloc_array(10);
    x[3] = 33;
    var y: i8[*] = fn4(x);
    print_i8(y[3]);
    free_array(y);
}

function main()
{
    test1();
    test2();
    test3();
    test4();
}
