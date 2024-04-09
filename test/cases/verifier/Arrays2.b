module Arrays2

import Test;

interface {}

function f1()
{
    var x = {1/0};     // Error
    ref r = x.0;       // Ref to "1/0"
    var y = r;         // read through the reference
    r = 1;             // write through the reference
}


function f2(ref a: i32[10])
{
    ref r = a[0];
    r = 1/0;          // Error, sets a[0] to "1/0"
    var y = r;        // r is now a ref to "1/0"; read the ref (should get no further error)
    r = 100;          // Write the ref (no further error)
}

function f4(x: bool[]): bool
    requires sizeof(x) > u64(0);
{
    // Regression test - this should work, but it was failing because the
    // compiler wasn't constructing the "valid" expression correctly
    return x[0];
}

// Testing array-projection where the LHS is an rvalue.
extern function make_array(): i32[*]
    ensures sizeof(return) == u64(10);

extern function f5()
    requires make_array()[0] == 1;
