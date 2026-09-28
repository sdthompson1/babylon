module UnivarFlags

// Tests for requirement flags on unification variables.

interface {}

datatype Maybe<a> = Nothing | Just(a);

ghost function h<U>(): U
{
    var u: U;
    return u;
}

function h2<U>(): U
{
    var u: U;
    return u;
}

function f1<T>(ghost z: T)
{
}

function f2<T>(ghost y: Maybe<T>, ghost z: T)
{
}

function k(ghost z: int)
{
}

function test1()
{
    ghost var n: int = int(1);
    f1(n);          // error: T := int, but T must be executable
    f2(h(), n);     // error: same, even though T was first reached via U := Maybe<T>
                    //   from the ghost argument h()
}

function test2()
{
    ghost var n: int = int(1);
    f2(h(), n);     // error: same again, with the calls in the other order
    f1(n);          // error
}

function test3()
{
    var v = h2();   // error: unable to infer type
}
