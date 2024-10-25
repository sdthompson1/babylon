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


