module OtherModule

interface {
    function f(x: i32): i32;

    ghost function f_lemma()
        ensures forall (xx: i32) f(xx) < 100;
}

function f(x: i32): i32
{
    return 10;
}

ghost function f_lemma()
    ensures forall (xx: i32) f(xx) < 100;
{}
