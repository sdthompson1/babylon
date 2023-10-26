module Main
interface {}

// This is checking that imported functions use the interface
// preconditions, not the implementation ones.

import Imported;

function test()
{
    var x1: i32 = Imported.foo(1);    // OK
    var x2: i32 = Imported.foo(0);    // Error, fails interface precond
    var x3: i32 = Imported.foo(-1);   // Error, fails both interface and impl preconds
}
