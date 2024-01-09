module Postcond2

interface {}

// Another regression test

extern function init<T>(ref x: T): bool
    ensures return ==> true;

function test<T>(ref x: {T}): bool
{
    // this should succeed (previously it was creating an invalid SMT problem)
    var result = init<{T}>(x);
    return result;
}

function fail()
{
    // create a verification error to prevent compilation
    // (we only want to test verifier in this test, not compiler)
    assert false;
}
