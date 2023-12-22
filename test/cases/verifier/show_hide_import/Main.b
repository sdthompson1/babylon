module Main

interface {}

import qualified Imported;

function test()
{
    hide Imported.f;
    assert Imported.f(1) == 1;  // fails
    show Imported.f;
    assert Imported.f(2) == 2;  // succeeds
}
