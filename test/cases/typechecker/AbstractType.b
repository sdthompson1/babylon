module AbstractType

interface {
    type Type1: Copy;
    function f(): Type1;
    function g(): {Type1, bool};

    type Type2: Move;
    function h(x: Type2): Type2;


    function id<A: Copy>(x: A): A

    {
        return x;
    }

    datatype Variant = V(Type1);

    ghost function test1()
    {
        var a: i32[3] = [1,2,3];
        var b: i8 = i8(1);
        var c: i32 = if true then 1 else 2;
        var d: i32 = -b;
        var e: i32 = let x = 1 in x + 1;
        var p: bool = forall (x:u32) x >= 0;
        var q: Type1 = id<Type1>(f());
        var r: {x: Type1, y: Type1} = {x = f(), y = f()};
        var s = {r with x = f()};
        var t: Type1 = r.x;
        var u: Variant = V(f());
        var w: Type1 = match u { case V(x) => x };
        var x: u64 = sizeof(a);

        var z: i32 = a[0];
    }


    type Abs2;



    type Abs6;

    type Abs8;




}

type Type1 = i32;

function f(): Type1
{
    return 100;
}

function g(): {Type1, bool}
{
    return 20;  // type error
}

datatype Type2 = A | B(i32) | C{i: i64, b: bool};

function h(x: Type2): Type2
{
    match x {
    case A => return B(0);
    case B(_) => return A;
    case C{i=i, b=b} => return C{i=i, b=false};
    }
}

type BadAbstractType;  // error - not allowed in implementation

datatype Abs7 = Abs7Ctor((bool[*])[10]);   // This is ok.
