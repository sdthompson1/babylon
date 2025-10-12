module Main

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
