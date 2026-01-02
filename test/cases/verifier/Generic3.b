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
    var x = Nothing;  // x :: Maybe<'a>    
    var y = get(x);   // y :: 'a
    assert y == 0;    // 'a now resolved to i32

    x = Just(100);
    y = get(x);
    assert y == 100;

    assert y == 99; // Should fail

    return y;
}
