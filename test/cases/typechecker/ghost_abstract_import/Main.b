module Main

interface {
    // A non-ghost abstract type cannot be implemented by an (imported)
    // ghost type.
    type BadAbs;
}

import Foo;

type BadAbs = Ghost;  // Error

ghost function test1(x: i32): bool
{
    // Ghost types can be used freely in ghost code.
    var g: Ghost = make_ghost(x);
    var n: Normal = make_normal();
    return true;
}

function test2()
{
    var n: Normal = make_normal();  // Should pass
    var g: Ghost;  // Should fail, Ghost cannot be used in executable code
}

function test3(): {Ghost, i32}  // Should fail, ghost type hidden inside a tuple
{
    return {make_ghost(1), 2};
}

function test4()
{
    ghost var g: Ghost = make_ghost(1);  // Should pass, this is a ghost variable
}
