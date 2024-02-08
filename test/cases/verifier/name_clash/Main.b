module Main

interface {}

// Regression test for a case where the verifier was getting confused
// because there were two variables named "xx".

import OtherModule;

function foo()
{
    ghost f_lemma();

    // This assert should succeed
    assert forall (xx: i32) f(xx) < 100;

    // This assert should fail
    assert forall (xx: i32) f(xx) < 50;
}
