module Main

interface {}

datatype Maybe<a> = Nothing | Just(a);

function is_just<T> (x: Maybe<T>): bool
{
    match x {
    case Nothing => return false;
    case Just(_) => return true;
    }
}

ghost function inspect(x: Maybe<i32>): i32;

extern function foo(): Maybe<i32>
    ensures is_just<i32>(return) ==> inspect(return) == 10;

function test()
{
    var v: Maybe<i32> = foo();
    match v {
    case Nothing => ;
    case Just(x) =>
        assert inspect(v) == 10;  // succeeds
        assert inspect(v) == 11;  // fails
    }
}
