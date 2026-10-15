module Foo

interface {
    ghost type T;
    datatype D = MkD(T);

    ghost function make_d(x: i32): D;
}

// Inside Foo, D could be used in executable code (see GhostRecompute.b),
// but importers can only see that T is ghost.
type T = i32;

ghost function make_d(x: i32): D
{
    return MkD(x);
}
