// Some basic type inference tests.

module Inference
interface {}

datatype Maybe<a> = Nothing | Just(a);

// Type inference works one statement at a time. In particular, the
// type of a variable must be fully determined by the end of the
// statement that declares it; later statements cannot be used to
// determine it.

function test1()
{
    var v = Nothing;    // Error, unable to infer type (v :: Maybe<?>).
    v = Just(1);        // This would have determined the type, but it is too late.
}

function test2(): i32
{
    var v: Maybe<bool> = Nothing;   // OK, with a type annotation.

    match v {
    case Nothing =>
        return 10;

    case Just(x) =>
        if x == false {       // OK, x :: bool
            return 10 + x;    // Fails, bool doesn't match i32
        } else {
            return 1 + (false + true);   // Can't add two bools. ("1 + type_error" is ignored.)
        }
    }
}

// The same rule applies to "let" (the type of the bound name must be
// inferred from the right-hand-side alone) and to pattern variables
// (the type must be inferred from the scrutinee alone).

ghost function test3(): bool
{
    return let m = Nothing in m == Just(1);   // Error, unable to infer type (for m).
}

function test4(): i32
{
    match Nothing {              // Error, unable to infer type (for x).
    case Just(x) => return x;
    case Nothing => return 0;
    }
}

// Within a single statement, the type of a sub-expression can be
// inferred from anywhere else in the statement.

function f32(x: Maybe<i32>) { }

function test5(): Maybe<i32>
{
    var v: Maybe<i32> = if true then Nothing else Just(1);   // OK, Nothing :: Maybe<i32>
    f32(Nothing);                                            // OK, Nothing :: Maybe<i32>
    return match v { case Just(x) => Just(x + 1) case Nothing => Nothing };  // OK, Nothing :: Maybe<i32>
}


// A type parameter that cannot be inferred at all is an error, even if
// it does not obviously affect anything (there is no "default" type).

ghost function all_equal<T>(): bool
{
    return forall (x: T) forall (y: T) x == y;
}

function test6()
{
    assert all_equal();          // Error, unable to infer type (for T).
    assert all_equal<{}>();      // OK
    assert Nothing == Nothing;   // Error, unable to infer type (for the type argument of Nothing).
    assert Nothing<i32> == Nothing;   // OK
}


function g<T>() { }

type MyTypedef = int;

function test7()
{
    var x: MyTypedef;   // Error, no 'int' in executable code.
    g<int>();           // Error, can't use 'int' as type-parameter in executable code.
    g<MyTypedef>();     // Error, ditto.
}


function from_just<T>(x: Maybe<T>): T
    // 'requires' conditions omitted
{
    return match x { case Just(a) => a };
}

function test8(): i32
{
    return from_just(Just{x=1, y=2}).x;
}

function test9(): u64
{
    var x: i32[10];
    return sizeof(from_just(Just(x)));
}

function test10(): i32
{
    return from_just(Just([1,2,3]))[0];
}
