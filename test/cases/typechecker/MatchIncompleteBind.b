module MatchIncompleteBind

// In a non-ghost match *statement*:
//  - the scrutinee must have a complete type, unless it's an lvalue; and
//  - all non-ref pattern variables must have complete types.

// The reason for these rules is that the pattern match compiler converts both non-lvalue
// scrutinees, and non-ref pattern variables, into local variables (like a "var" statement).
// The code generator needs to track ownership of such variables, so it requires them not
// to have incomplete types.

// (For match terms, these rules are waived, because the match compiler uses "let" instead
// of "var" in this case, and ownership issues don't arise with "let". Similarly, in ghost
// code, ownership is not an issue, so the above rules don't apply for ghost code.)

interface {}

datatype Foo = Foo(i32[]);

function nonlvalue_scrutinee(c: bool, ref r: i32[], ref s: i32[]): u64
{
    match (if c then r else s) {      // error: non-lvalue scrutinee with incomplete type
    case _ => return u64(0);
    }
}

function byvalue_pattern_var(ref r: i32[]): u64
{
    match r {
    case x => return sizeof(x);       // error: non-ref variable x with incomplete type
    }
}

function byvalue_payload(f: Foo): u64
{
    match f {
    case Foo(x) => return sizeof(x);  // error: non-ref variable x with incomplete type
    }
}

function ref_pattern_var(ref r: i32[]): u64
{
    match r {
    case ref x => return sizeof(x);   // ok (scrutinee is lvalue, and x is "ref" not "var")
    }
}

function ref_payload(f: Foo): u64
{
    match f {
    case Foo(ref x) => return sizeof(x);   // ok (scrutinee lvalue, and x is "ref")
    }
}

function lvalue_scrutinee_wildcard(ref r: i32[]): u64
{
    match r {                          // ok: scrutinee is lvalue
    case _ => return sizeof(r);
    }
}

ghost function ghost_copies(c: bool, ref r: i32[], ref s: i32[]): u64
{
    match (if c then r else s) {       // ok: ghost code, above rules do not apply
    case x => return sizeof(x);
    }
}

function match_term(c: bool, a: i32[], b: i32[]): u64
{
    // ok: match term (not statement), so the above rules do not apply
    return
        match (if c then a else b) {
            case x => sizeof(x)
        };
}
