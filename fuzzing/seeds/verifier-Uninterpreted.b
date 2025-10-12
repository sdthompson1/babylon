module Main

interface {}

ghost function f(): i8;     // Uninterpreted ghost function
ghost const c: i32;         // Uninterpreted ghost constant

function test()
{
    assert f() == f();
    assert c == c;
    assert c == 0;  // Fails
}

function test2()
{
    assert f() == 0; // Fails
}

function test3()
{
    // Test the assume statement
    assume c > 35;
    assert c > 30;  // Succeeds
    assert c > 40;  // Fails e.g. c could be 36
}

function test4()
{
    // We can use assume to prove false statements...
    assert 0 == 1         // No error raised
    {
        assume false;
    }
}

function test5()
{
    assert f() <= 127;   // Should be true since return type is i8
}

ghost function f2(ref x: i32): bool;

function test6()
{
    ghost var v = 1;
    ghost var f2v = f2(v);
    assert f2v == true || f2v == false;
}


// Uninterpreted function with precondition.
ghost function with_precond(x: i32): bool;
    requires x > 10;

function test7()
{
    ghost var v1 = with_precond(20);
    ghost var v2 = with_precond(5);   // Error, precondition not met.
}
