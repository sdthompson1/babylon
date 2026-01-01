module ArrayLit

interface {}

function test1()
{
    var a = [1, 2, 3];
    assert a[1] == 2;
    assert sizeof(a) == u64(3);
    assert a[2] == 99;  // negative test
}

function test2()
{
    var a = [1, 2, 3/0, 4];  // verification error in one of the elements
    assert a[0] == 1;  // succeeds
}

ghost function return_array(x: i32): i32[]
{
    return [x];
}

ghost function test3()
{
    var arr = return_array(99);
    assert arr[0] == 99;  // Should succeed
}
