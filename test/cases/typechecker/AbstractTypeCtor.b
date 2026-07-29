module AbstractTypeCtor

// Abstract types in a data-constructor payload.

interface {
    type T;
    datatype Foo = MkFoo(T) | Other | Rec{a: T, b: bool};

    function get(f: Foo): i32;
    function test();
}

datatype Bar = Bar(i32);
type T = Bar;

function get(f: Foo): i32
{
    match f {
    case MkFoo(Bar(i)) => return i;
    case Other => return 0;
    case Rec{a = Bar(i), b = flag} => return if flag then i else 0;
    }
}

function main()
{
    var x: T = Bar(10);

    var y: Foo = MkFoo(x);  // ok
    assert get(y) == 10;

    var z: Foo = Rec{a = Bar(20), b = true};  // ok
    assert get(z) == 20;

    assert get(Other) == 0;  // ok

    var bad: Foo = MkFoo(100);  // error, T is not i32
}
