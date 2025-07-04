module IntReal

interface {}

ghost function f1(i: i32)
{
    // Basic tests
    assert int(1) + int(2) == int(3);
    assert real(3) / real(2) == real(1) + real(1) / real(2);

    // Casting real to int gives "floor" behaviour
    assert int(real(5) / real(4)) == int(1);
    assert int(real(-5) / real(4)) == int(-2);

    // Casting i32 to int or real and back again
    assert i32(int(i)) == i;
    assert i32(real(i)) == i;
}

ghost function f2(i: int)
{
    var j = i8(i);    // error, out of range
}

ghost function f3(i: int)
    requires int(-128) <= i <= int(127);
{
    var j = i8(i);    // ok
}

ghost function f4()
{
    // Defaults
    var i: int;
    var r: real;
    assert i == int(0);
    assert r == real(0);
}

ghost function f5()
{
    // Division of integers
    assert int(1000) / int(13) == int(76);
    assert int(1000) % int(13) == int(12);
    assert int(-1000) / int(-13) == int(76);
    assert int(-1000) % int(-13) == int(-12);
    assert int(1000) / int(-13) == int(-76);
    assert int(1000) % int(-13) == int(12);
    assert int(-1000) / int(13) == int(-76);
    assert int(-1000) % int(13) == int(-12);

    // Division by zero
    var i = int(10) / int(0);   // error
}

ghost function f6()
{
    // Modulo zero
    var i = int(10) % int(0);   // error
}

ghost function f7()
{
    // Division of reals
    assert real(1) < real(3)/real(2) < real(2);

    // Division by zero
    var r = real(1) / real(0);   // error
}

ghost function f8()
{
    // Decreases integer
    var i: int = int(1000);
    while i > int(10)
        decreases i;
    {
        i = i - int(1);
    }

    // Decreases nested tuple of integers
    var j: {int,{int,int}} = {int(10), {int(20), int(30)}};
    while (j != {int(0), {int(0), int(0)}})
        invariant j.0 >= int(0);
        invariant j.1.0 >= int(0);
        invariant j.1.1 >= int(0);
        decreases j;
    {
        j.1.1 = j.1.1 - int(1);
        if j.1.1 < int(0) {
            j.1.1 = int(10);
            j.1.0 = j.1.0 - int(1);
            if j.1.0 < int(0) {
                j.1.0 = int(10);
                j.0 = j.0 - int(1);
            }
        }
    }
}

ghost function f9()
{
    // Decreases without lower bound - not allowed
    var i: int = int(1000);
    while true
        decreases i;     // Error: not bounded below
    {
        i = i - int(1);
    }
}

ghost function f10()
{
    // Decreases without lower bound in one component of tuple
    var i: {int, {int, int}} = {int(10), {int(11), int(10)}};

    while (i != {int(0), {int(0), int(0)}})
        invariant i.0 >= int(0);
        invariant i.1.1 >= int(0);
        decreases i;   // error: i.1.0 is unbounded
    {
        i.0 = i.0 - int(1);
        i.1.0 = i.1.0 - int(2);
        i.1.1 = i.1.1 - int(1);

        if i.0 < int(0) { i.0 = int(0); }
        if i.1.1 < int(0) { i.1.1 = int(0); }
    }
}
