module Main

interface {}

extern impure function ext_impure(): i32;
extern function ext_pure(): i32;

impure function test1()
{
    var p1 = ext_pure();
    var p2 = ext_pure();
    var i1 = ext_impure();
    var i2 = ext_impure();
    assert p1 == p2;  // Succeeds
    assert i1 == i2;  // Fails - impure function might return different results each time it's called.
}

impure function test2()
{
    var i1 = ext_impure();
    var i2 = ext_impure();
    assert i1 != i2;  // Also fails - impure function need not return different results!
}


extern impure function foo(x: i32, y: i32): i32
    requires 0 <= x <= 10;
    requires 0 <= y <= 10;
    ensures x + y - 5 <= return <= x + y + 5;

impure function test3()
{
    var i1 = foo(10, 5);
    assert 10 <= i1 <= 20;  // succeeds
    assert i1 == 10;  // fails
}

impure function test4()
{
    var i1 = foo(99, 10);   // fails precondition
}


impure function test5(): i32
{
    return 100;
}

impure function test6()
{
    var i = test5();

    // This fails, because the verifier assumes that an impure function might return
    // a different result every time it is called, therefore it doesn't even bother to
    // look inside the function body (which is a trivial "return 100" in this case).
    assert i == 100;
}


// Further tests: Impure function with no return type, or with ref args.

impure function void_fn() {}

impure function ref_fn(ref x: i32, ref y: i32): i32 { return 0; }

impure function test7(b1: bool)
{
    void_fn();

    var i: i32 = 1;
    var j: i32 = 2;
    var k = ref_fn(i, j);
    assert k == k; // ok
    if b1 {
        assert i == 1;  // should fail
    } else {
        assert k == 0;  // should fail
    }
}
