module Arrays6

interface {}

function f1(ref a: i32[])
    requires sizeof(a) > u64(10);
    requires a[10] < 10000;
{
    a[10] = a[10] + 1;
}

function test1()
{
    var a: i32[20];
    var i: i32 = 0;
    while i < 10
        decreases ~i;
        invariant i <= 10;
        invariant a[10] == i;
    {
        f1(a);
        i = i + 1;
    }
    assert a[10] == 10;
    assert a[10] == 11;  // negative test
}

function f2(ref a: i32[], ref b: i32[])
{
}

function f3(ref a: i32[11], ref b: i32[])
{
}

function f4(ref a: i32[], ref b: i32)
{
}

function test2()
{
    var a: i32[10][11];
    f2(a[2], a[2]);     // aliasing violation
    f3(a[2], a[2]);     // aliasing violation
    f4(a[2], a[2][4]);  // aliasing violation
}

ghost function test3()
{
    var a: i32[];  // this is now allowed (in ghost code only) but can only make an array of size 0
    assert sizeof(a) == u64(0);
}
