module ReservedNames

interface {
    function main();
}

import Test;

function foo(): {i32, i32}
{
    // Leading underscore + upper letter is reserved for the C compiler,
    // as is leading double underscore
    var _Leading_underscore = 1;
    print_i32(_Leading_underscore);

    var __leading_double_underscore = 2;
    print_i32(__leading_double_underscore);

    // The compiler makes temporary variables with names like "tmp0" so these
    // should not clash with user identifiers
    var tmp0 = 3;
    print_i32(tmp0);

    // "tmp" followed by non-digits should be ok
    var tmpz = 4;
    print_i32(tmpz);

    // The compiler also uses "ret" as a temporary identifier
    var ret = 5;
    print_i32(ret);

    // "enum" would clash with a C keyword
    var enum = 6;
    print_i32(enum);

    // "memcpy", "memmove", "memset" would clash with C function names
    var memcpy = 7;
    var memmove = 8;
    var memset = 9;
    print_i32(memcpy);
    print_i32(memmove);
    print_i32(memset);

    // Create a tuple and return it, which will exercise memset, memcpy,
    // and the reserved "ret" variable
    var x: {i32, i32};
    return x;
}

function main()
{
    var y = foo();
    print_i32(y.0);
    print_i32(y.1);
}
