module Foo

interface {
    // A "ghost" abstract type. Because it is ghost, it is allowed to be
    // implemented by a non-runtime type (see below), but in return, it
    // cannot be used in executable code.
    ghost type Ghost;

    ghost function make_ghost(x: i32): Ghost;

    // A "normal" abstract type, for comparison.
    type Normal;

    function make_normal(): Normal;
}

type Ghost = int;

ghost function make_ghost(x: i32): Ghost
{
    return int(x);
}

type Normal = i32;

function make_normal(): Normal
{
    return 0;
}
