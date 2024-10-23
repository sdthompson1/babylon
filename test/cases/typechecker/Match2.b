module Match2

interface {}

datatype A<T> = A(T);

extern function foo<T>(ref x: A<T>);

function test()
{
    var v = A{};
    foo(v);

    // To typecheck the "case" pattern below, the typechecker needs to chase
    // unification variables in the type of v:
    match v {
    case A{} =>
    }

    // A negative test:
    match v {
    case A(100) =>
    }
}

function test2()
{
    match {1,2,3,4} {
    case {3, 6, x, y} =>
        x = 99;   // this is ok: x is "copied"

    case {ref x, y, _, _} =>
        x = 99;   // error: x is a ref to a readonly expression (a temporary)
    }
}


