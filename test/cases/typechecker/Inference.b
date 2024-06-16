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
            x = x - real(1);  // This should infer x :: real, which then fails the constraint (real is not valid for decreases).
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
    var x = Nothing;   // This line is OK, type of x is not known yet.
    ghost f(x);   // This is trying to give x the type Maybe<real>, which is illegal in executable code.
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


function g<T>() { }

type MyTypedef = int;

function test7()
{
    var x: MyTypedef;   // Error, no 'int' in executable code.
    g<int>();           // Error, can't use 'int' as type-parameter in executable code.
    g<MyTypedef>();     // Error, ditto.
}
