module Main

interface {}

import AbstractType;

function f1<T: Move>() {}

function test()
{
    f1<Abstr>();  // ok, Abstr exports Copy, hence it also has Move.

    var v: Abstr;   // error, Abstr doesn't export Default, so can't default-init.
}
