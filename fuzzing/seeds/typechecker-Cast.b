module Main

interface {}

type Foo = i32;

datatype Maybe<a> = Just(a) | Nothing;

function test()
{
    var x: i8;
    var c1 = i32(x);
    var c2 = cast<i32>(x);
    var c3 = cast<Foo>(x);

    var err1 = cast<Maybe>(x);  // Kind error
    var err2 = cast<Maybe<i32> >(x);  // Cannot cast to Maybe
}
