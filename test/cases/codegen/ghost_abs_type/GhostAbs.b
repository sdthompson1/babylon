module GhostAbs

interface {
    // "Model" is a ghost abstract type: it exists only for specification
    // purposes, so it is allowed to be implemented by a non-runtime type
    // (in this case, "int").
    ghost type Model;

    ghost function model_of(x: i32): Model;
    ghost function value_of(m: Model): int;

    function double(x: i32): i32
        requires -1000 <= x;
        requires x <= 1000;
        ensures value_of(model_of(return)) == int(2) * value_of(model_of(x));
}

type Model = int;

ghost function model_of(x: i32): Model
{
    return int(x);
}

ghost function value_of(m: Model): int
{
    return m;
}

function double(x: i32): i32
    requires -1000 <= x;
    requires x <= 1000;
    ensures value_of(model_of(return)) == int(2) * value_of(model_of(x));
{
    return x * 2;
}
