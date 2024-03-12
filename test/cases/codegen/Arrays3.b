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
    var a: i32[*,*];
    resize_2d_array<i32>(a, 10, 8);

    a[3,3] = 3333;

    f1(a);

    print_i32(a[0,0]);
    print_i32(a[9,7]);
    print_i32(a[3,3]);
    print_i32(a[1,1]);

    resize_2d_array<i32>(a, 0, 0);
}

function test3()
{
    var a: i32[*,*];
    resize_2d_array<i32>(a, 10, 20);

    a[3,3] = 3333;

    f2(a);
    
    print_i32(a[0,0]);
    print_i32(a[9,7]);
    print_i32(a[3,3]);
    print_i32(a[1,1]);

    resize_2d_array<i32>(a, 0, 0);
}

function main()
{
    test1();
    test2();
    test3();
}
