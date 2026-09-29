module MatchRefExpr

// 'ref' pattern variables are allowed in match statements, but not in
// match expressions. (A match expression cannot write through a pattern
// variable, and it never copies the matched value, so 'ref' would make
// no difference there.)

interface {}

datatype D = Mk(i32);

function rvalue(): D
{
    return Mk(1);
}

function exec_code(ref r: i32[10], d: D)
{
    var v: D = Mk(50);

    // Scrutinee is an lvalue
    var n1 = match r { case ref x => sizeof(x) };          // Error
    var n2 = match v { case Mk(ref x) => x };              // Error
    var n3 = match d { case Mk(ref x) => x };              // Error
    var n4 = match {v, 1} { case {ref x, _} => 1 };        // Error

    // Scrutinee is not an lvalue
    var n5 = match rvalue() { case Mk(ref x) => x };       // Error
    var n6 = match 1 + 2 { case ref x => x };              // Error

    // Without 'ref', all of these are fine
    var m1 = match r { case x => sizeof(x) };
    var m2 = match v { case Mk(x) => x };
    var m3 = match d { case Mk(x) => x };
    var m4 = match {v, 1} { case {x, _} => 1 };
    var m5 = match rvalue() { case Mk(x) => x };
    var m6 = match 1 + 2 { case x => x };

    // Match statement over an lvalue: 'ref' is still allowed
    match v {
    case Mk(ref x) => x = 10;
    }
    match r {
    case ref x => x[0] = 10;
    }
}

function nested(d: D): i32
{
    // Match expression nested inside a match statement
    match d {
    case Mk(ref y) =>
        return match d { case Mk(ref x) => x };            // Error
    }
}

ghost function ghost_code(ref r: i32[10], d: D): i32
{
    var v: D = Mk(50);

    var n1 = match r { case ref x => sizeof(x) };          // Error
    var n2 = match v { case Mk(ref x) => x };              // Error
    var n3 = match rvalue() { case Mk(ref x) => x };       // Error
    assert match d { case Mk(ref x) => x == x };           // Error

    var m1 = match r { case x => sizeof(x) };
    var m2 = match v { case Mk(x) => x };
    var m3 = match rvalue() { case Mk(x) => x };
    assert match d { case Mk(x) => x == x };

    match v {
    case Mk(ref x) => x = 10;
    }

    return match v { case Mk(ref x) => x };                // Error
}

function spec(ref x: i32, d: D)
    requires match d { case Mk(ref y) => y == 0 };         // Error
    requires match d { case Mk(y) => y == 0 };
    ensures match x { case ref y => y == 0 };              // Error
    ensures match x { case y => y == 0 };
{
    x = 0;
}
