// Some basic type inference tests.

module Inference
interface {}

datatype Maybe<a> = Nothing | Just(a);

function test(): i32
{
    var v = Nothing;
    
    match v {
    case Nothing =>
        return 10;
        
    case Just(x) =>
        if x == false {       // Succeeds, infers v :: Maybe<bool>, x :: bool
            return 10 + x;    // Fails, bool doesn't match i32
        } else {
            return 1 + (false + true);   // Can't add two bools. ("1 + type_error" is ignored.)
        }
    }
}

ghost function test2()
{
    var v = Nothing;
    match v {
    case Just(ref x) =>
        while true
            decreases x;     // Adds constraint: typeof(x) must be valid-for-decreases.
        {
            x = x - real(1);  // this is now valid from typechecking pov (but verifier won't verify it).
        }
    }
}

ghost function test3(): bool
{
    var a = Nothing;    // Maybe<alpha>
    var b = Nothing;    // Maybe<beta>
    match {a, b} {
    case {x, y} =>
        // This forces alpha = beta but does not otherwise constrain the type:
        return x == y;
    }
}

function test4(): bool
{
    var a = Nothing;
    var b = Nothing;
    match {a, b} {
    case {x, y} =>
        // Just like in test3, x and y will now have type "alpha" (where alpha is a 
        // unification variable).
        // But in executable code, == can only be used at certain types, so we need
        // to impose something like an "Eq alpha" constraint (or just commit to a
        // particular type at this point). Unfortunately, the typechecker isn't
        // currently smart enough to do either of those things, so the following ends
        // up being an error at the moment.
        return x == y;
    }
}

ghost function f(x: Maybe<real>)
{
}

function test5()
{
    var x = Nothing;   // This line is OK, x is given type Maybe<alpha_Move>.
    ghost f(x);   // Error, can't unify "alpha_Move" with "real".
}

function f64(x: Maybe<i64>) { }
function f32(x: Maybe<i32>) { }

function test6(): Maybe<i64>
{
    var v = Nothing;    // v has type Maybe<alpha>, for some unknown alpha.
    if false {
        f64(v);   // v now has type Maybe<i64>.
    } else {
        f32(v);   // Error, v is Maybe<i64>, doesn't match Maybe<i32>.
    }
}


function g<T: Copy>() { }

type MyTypedef = int;

function test7()
{
    var x: MyTypedef;   // Error, 'int' doesn't have Default trait
    g<int>();           // Error, 'int' doesn't have Copy trait
    g<MyTypedef>();     // Error, 'MyTypedef' doesn't have Copy trait
}


function from_just<T: Copy>(x: Maybe<T>): T
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
