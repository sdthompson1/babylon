module Main

interface {
    function main()
}

import Test;

function scalar_swap()
{
    var x = 1;
    var y = 2;
    
    ref rx = x;
    ref ry = y;

    swap x, y;
    print_i32(x);
    print_i32(y);

    swap rx, y;
    print_i32(x);
    print_i32(y);

    swap x, ry;
    print_i32(x);
    print_i32(y);

    swap rx, ry;
    print_i32(x);
    print_i32(y);
}

function aggregate_swap()
{
    var a = {1, 2, 3};
    var b = {4, 5, 6};
    swap a, b;
    
    print_i32(a.0);
    print_i32(a.1);
    print_i32(a.2);
    print_i32(b.0);
    print_i32(b.1);
    print_i32(b.2);

    ref ra = a;
    ref rb = b;
    swap ra, rb;
    
    print_i32(a.0);
    print_i32(a.1);
    print_i32(a.2);
    print_i32(b.0);
    print_i32(b.1);
    print_i32(b.2);
}

function swap_scalar_with_field()
{
    var a = 1;
    var b = {2, 3, 4};

    swap a, b.0;
    
    print_i32(a);
    print_i32(b.0);
    print_i32(b.1);
    print_i32(b.2);

    ref ra = a;
    ref rb1 = b.1;
    
    swap rb1, ra;

    print_i32(a);
    print_i32(b.0);
    print_i32(b.1);
    print_i32(b.2);
}

function swap_fields()
{
    var a = {1, 2, 3};
    var b = {4, 5, 6};

    swap a.1, b.2;

    print_i32(a.0);
    print_i32(a.1);
    print_i32(a.2);
    print_i32(b.0);
    print_i32(b.1);
    print_i32(b.2);

    ref ra2 = a.2;
    ref rb0 = b.0;

    swap ra2, rb0;

    print_i32(a.0);
    print_i32(a.1);
    print_i32(a.2);
    print_i32(b.0);
    print_i32(b.1);
    print_i32(b.2);
}

function self_swap()
{
    var a = 1;
    swap a, a;
    print_i32(a);

    var x = {1, 2, 3};
    swap x, x;
    print_i32(x.0);
    print_i32(x.1);
    print_i32(x.2);

    swap x.1, x.1;
    print_i32(x.0);
    print_i32(x.1);
    print_i32(x.2);
}

function main()
{
    scalar_swap();
    aggregate_swap();
    swap_scalar_with_field();
    swap_fields();
    self_swap();
}
