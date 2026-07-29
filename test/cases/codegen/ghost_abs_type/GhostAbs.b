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

    // A ghost argument is erased before codegen, so it is allowed to
    // have a ghost type, even though "double_checked" is not a ghost
    // function. (The caller sees "Model" as an abstract ghost type.)
    function double_checked(x: i32, ghost m: Model): i32
        requires m == model_of(x);
        requires -1000 <= x;
        requires x <= 1000;
        ensures value_of(model_of(return)) == int(2) * value_of(m);
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

function double_checked(x: i32, ghost m: Model): i32
    requires m == model_of(x);
    requires -1000 <= x;
    requires x <= 1000;
    ensures value_of(model_of(return)) == int(2) * value_of(m);
{
    return x * 2;
}
