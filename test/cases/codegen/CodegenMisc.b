module CodegenMisc

// This test is to cover some lines in codegen.c that are not being
// covered anywhere else.

interface {
    function main();
}

import Test;

const c_int_tuple = {10, 20, 30};

function f(): i32
{
    return 42;
}

function main()
{
    var v1 = c_int_tuple;
    print_i32(v1.1);

    ref r0 = v1.0;
    ref r2 = v1.2;
    r0 = r2;
    print_i32(v1.0);

    var v2 = {false && false, true || true, false ==> true};
    print_bool(v2.0);
    print_bool(v2.1);
    print_bool(v2.2);

    var v3 = {f(), 1};
    print_i32(v3.0);

    var a: i32[];
    var v4 = {sizeof(a), 1000};
    print_u64(v4.0);
}
