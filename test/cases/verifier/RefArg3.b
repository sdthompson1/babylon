module RefArg3
interface {}

function foo(dummy: bool, ref arr: i32[])
    requires sizeof(arr) == u64(10);
    ensures sizeof(arr) == old(sizeof(arr));
    ensures arr[5] == 1;
{
    arr[5] = 1;   // OK
    arr[15] = 0;  // Error
}


// Passing something by ref in a return-expression

function f1(ref x: i32): i32
    requires 0 <= x <= 10;
{
    x = x + 1;
    return x + 2;
}

function call_f1(ref x: i32): i32
    requires 0 <= x <= 8;
{
    x = x + 2;
    return f1(x);
}

function f2(ref x: i32)
    requires 0 <= x <= 8;
{
    ghost var old_x = x;
    
    var r = call_f1(x);
    
    assert x == old_x + 3;
    assert r == old_x + 5;
}
