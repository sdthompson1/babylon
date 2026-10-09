module Uninterpreted

interface {}

ghost extern function f(): i8;     // Uninterpreted ghost function


function test()
{
    assert f() == f();


}

function test2()
{
    assert f() == 0; // Fails
}

function test3()
{
    // Test the assume statement
    assume f() > 35;
    assert f() > 30;  // Succeeds
    assert f() > 40;  // Fails e.g. f() could be 36
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

ghost extern function f2(ref x: i32): bool;

function test6()
{
    ghost var v = 1;
    ghost var f2v = f2(v);
    assert f2v == true || f2v == false;
}


// Uninterpreted function with precondition.
ghost extern function with_precond(x: i32): bool;
    requires x > 10;

function test7()
{
    ghost var v1 = with_precond(20);
    ghost var v2 = with_precond(5);   // Error, precondition not met.
}
