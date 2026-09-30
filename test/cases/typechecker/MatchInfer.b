module MatchInfer

// The type of a match scrutinee must be determined by the scrutinee
// expression alone. Patterns are checked against the scrutinee type;
// they never contribute to type inference.

// There is no "default" type either, so a match whose scrutinee type
// contains an undetermined type argument is always an error, and it
// is always the same error ("Unable to infer type", reported at the
// scrutinee), whatever the patterns are. The fix is to determine the
// type in the scrutinee itself, e.g. by giving an explicit type
// argument.

interface {}

datatype Maybe<a> = Nothing | Just(a);

function h<U>(): U
{
    var u: U;
    return u;
}

function g<U>(): Maybe<U>
{
    return Nothing;
}

function f<T>(x: Maybe<T>): i32
{
    return 0;
}


// Match statements, scrutinee h() (the whole type is undetermined).

function stmt_h()
{
    match h() {            // Error, unable to infer type
    case Just(_) =>
    case Nothing =>
    }

    match h() {            // Error, unable to infer type
    case Just(x) =>
    case Nothing =>
    }

    match h() {            // Error, unable to infer type
    case {_, _} =>
    }

    match h() {            // Error, unable to infer type
    case {a = _} =>
    }

    match h() {            // Error, unable to infer type
    case true =>
    case false =>
    }

    match h() {            // Error, unable to infer type
    case 1 =>
    case _ =>
    }

    match h() {            // Error, unable to infer type (same as "var v = h();")
    case v =>
    }

    match h() {            // Error, unable to infer type (even though nothing is inspected or bound)
    case _ =>
    }

    // These patterns could not all match the same type, but the patterns
    // are not checked if the type of the scrutinee is unknown.
    match h() {            // Error, unable to infer type
    case Just(_) =>
    case 1 =>
    case true =>
    }
}


// Match statements, scrutinee g() (the type is known to be Maybe<?>,
// but the payload type is not known).

function stmt_g()
{
    match g() {            // Error, unable to infer type
    case Just(x) =>
    case Nothing =>
    }

    match g() {            // Error, unable to infer type
    case Just(_) =>
    case Nothing =>
    }

    // The inner patterns do not determine the payload type.
    match g() {            // Error, unable to infer type
    case Just(true) =>
    case Nothing =>
    case Just(false) =>
    }

    match g() {            // Error, unable to infer type
    case Just(1) =>
    case _ =>
    }

    match g() {            // Error, unable to infer type
    case Just(Just(_)) =>
    case _ =>
    }
}


// The scrutinee type can be determined by an explicit type argument.

function stmt_ok(): i32
{
    match h<Maybe<i32>>() {
    case Just(x) =>
    case Nothing =>
    }

    match g<i32>() {
    case Just(_) =>
    case Nothing =>
    }

    match h<{i32, bool}>() {
    case {_, true} =>
    case {_, false} =>
    }

    match h<bool>() {
    case true =>
    case false =>
    }

    match h<i8>() {
    case 1 =>
    case _ =>
    }

    match g<bool>() {
    case Just(true) =>
    case Nothing =>
    case Just(false) =>
    }

    match g<Maybe<i32>>() {
    case Just(Just(_)) =>
    case _ =>
    }

    match h<i32>() {
    case v => return v;
    }
}


// A type argument that is undetermined, but that does not appear in the
// type of the scrutinee. (Here the scrutinee has type i32.)

function stmt_f()
{
    // The patterns are fine. The error comes from the usual rule that
    // no type may be left undetermined at the end of a statement.
    match f(Nothing) {     // Error, unable to infer type (for the type argument of f)
    case 1 =>
    case _ =>
    }

    // The patterns are checked, because the type of the scrutinee is known.
    match f(Nothing) {
    case true =>           // Error, type mismatch in pattern
    case _ =>
    }

    match f(Nothing<bool>) {
    case 1 =>
    case _ =>
    }
}


// Match expressions. The expected type of the statement determines
// the type of the arms, but never the type of the scrutinee.

function expr_h()
{
    var n1: i32 = match h() {  // Error, unable to infer type
        case Just(_) => 1
        case Nothing => 2
    };

    var n2: i32 = match h() {  // Error, unable to infer type
        case Just(x) => 1
        case Nothing => 2
    };

    var n3: i32 = match h() {  // Error, unable to infer type
        case {_, _} => 1
    };

    var n4: i32 = match h() {  // Error, unable to infer type
        case true => 1
        case false => 2
    };

    var n5: i32 = match h() {  // Error, unable to infer type
        case 1 => 1
        case _ => 2
    };

    var n6: i32 = match h() {  // Error, unable to infer type
        case v => 1
    };

    var n7: i32 = match h() {  // Error, unable to infer type
        case _ => 1
    };

    // The type of the scrutinee is not inferred from the use of the
    // pattern variable in the arm (nor from the expected type of the match).
    var n8: i32 = match h() {  // Error, unable to infer type
        case v => v
    };
}

function expr_g()
{
    var n1: i32 = match g() {  // Error, unable to infer type
        case Just(x) => 1
        case Nothing => 2
    };

    var n2: i32 = match g() {  // Error, unable to infer type
        case Just(_) => 1
        case Nothing => 2
    };

    var n3: i32 = match g() {  // Error, unable to infer type
        case Just(true) => 1
        case Nothing => 2
        case Just(false) => 3
    };

    var n4: i32 = match g() {  // Error, unable to infer type
        case Just(x) => x
        case Nothing => 2
    };
}

function expr_f()
{
    var n1: i32 = match f(Nothing) {  // Error, unable to infer type (for the type argument of f)
        case 1 => 1
        case _ => 2
    };

    var n2: i32 = match f(Nothing) {
        case true => 1                // Error, type mismatch in pattern
        case _ => 2
    };

    var n3: i32 = match f(Nothing<bool>) {
        case 1 => 1
        case _ => 2
    };
}

function expr_ok(): i32
{
    var n1: i32 = match h<Maybe<i32>>() {
        case Just(x) => x
        case Nothing => 2
    };

    var n2: i32 = match g<i32>() {
        case Just(_) => 1
        case Nothing => 2
    };

    var n3 = match g<bool>() {
        case Just(true) => 1
        case Nothing => 2
        case Just(false) => 3
    };

    return match h<i32>() { case v => v };
}


// None of this depends on whether the code is ghost or executable.

ghost function ghost_h(): i32
{
    match h() {            // Error, unable to infer type
    case Just(_) =>
    case Nothing =>
    }

    match h() {            // Error, unable to infer type
    case true =>
    case false =>
    }

    match h() {            // Error, unable to infer type
    case v =>
    }

    match h() {            // Error, unable to infer type
    case _ =>
    }

    return match h() {     // Error, unable to infer type
        case Just(_) => 1
        case Nothing => 2
    };
}

ghost function ghost_g(): i32
{
    match g() {            // Error, unable to infer type
    case Just(x) =>
    case Nothing =>
    }

    match g() {            // Error, unable to infer type
    case Just(_) =>
    case Nothing =>
    }

    match g() {            // Error, unable to infer type
    case Just(true) =>
    case Nothing =>
    case Just(false) =>
    }

    return match g() {     // Error, unable to infer type
        case Just(x) => 1
        case Nothing => 2
    };
}

ghost function ghost_ok(): i32
{
    match h<Maybe<i32>>() {
    case Just(x) =>
    case Nothing =>
    }

    match g<i32>() {
    case Just(_) =>
    case Nothing =>
    }

    return match g<i32>() {
        case Just(x) => x
        case Nothing => 2
    };
}

function ghost_stmts()
{
    ghost match h() {      // Error, unable to infer type
    case Just(_) =>
    case Nothing =>
    }

    ghost match g() {      // Error, unable to infer type
    case Just(_) =>
    case Nothing =>
    }

    ghost match g<i32>() {
    case Just(_) =>
    case Nothing =>
    }

    assert match g() {     // Error, unable to infer type
        case Just(_) => true
        case Nothing => true
    };

    assert match g<i32>() {
        case Just(_) => true
        case Nothing => true
    };
}
