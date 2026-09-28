module Generic3
interface { }

datatype Maybe<a> = Nothing | Just(a);

function get<a>(x: Maybe<a>): a
    requires forall (x: a) !allocated(x);
{
    match x {
    case Just(i) => return i;
    case Nothing =>
        var dflt: a;
        return dflt;
    }
}

function f(): i32
{
    var x: Maybe<i32> = Nothing;
    var y = get(x);   // y :: i32
    assert y == 0;

    x = Just(100);
    y = get(x);
    assert y == 100;

    assert y == 99; // Should fail

    return y;
}
