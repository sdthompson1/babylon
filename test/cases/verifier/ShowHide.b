module ShowHide

interface {}

function f(): i32
    ensures return > 0;
{
    return 1;
}

function g(x: i32): i32
{
    return x;
}

function test1()
{
    assert f() == 1;  // succeeds
}

function test2()
{
    hide f;
    assert f() == 1;  // fails, body of f is hidden
    assert f() > 0;   // succeeds, postconditions of f are still visible
}

function test3()
{
    hide f;
    show f;
    assert f() == 1;  // succeeds
}

function test4()
{
    assert f() == 1;
    hide f;
    assert f() == 1;  // succeeds because it can use the earlier assert
}

function test5()
{
    if 1 == 1 {
        hide f;
    }

    assert f() == 1;  // succeeds because "show" and "hide" are block-scoped
}

function test6()
{
    // another scope test
    while false
        decreases 0;
    {
        hide f;
    }

    assert f() == 1;
}

function test7()
{
    // another scope test
    match true
    {
    case true =>
        hide f;
    case false =>
        hide f;
    }

    assert f() == 1;
}

function test8()
{
    hide f;
    hide g;

    if true {
        // override earlier "hide" in a nested scope
        show f;
        show g;
        assert f() == 1;   // succeeds
    }

    assert g(2) == 2;   // fails because g now hidden again
}

function test9()
{
    var i: i32 = 10;
    while i > 0
        invariant g(i) == i;
        decreases i;
    {
        i = i - 1;
        hide g;
        // error: invariant now fails to prove.
        // (This is testing that the scope of the "hide" covers the proof
        // that the invariants still hold on exit from the loop.)
    }
}

function test10()
{
    // Scope test: hide/show included in a "proof" of an assert
    // should be limited to the scope of the proof

    assert 1 == 1 {
        hide g;
    }

    assert g(3) == 3;   // should succeed, g is now shown again
}
