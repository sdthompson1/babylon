module MatchIncompleteBind

// In a non-ghost match *statement*, all non-ref pattern variables must have
// complete types.

// The reason for this rule is that the pattern match compiler converts
// non-ref pattern variables into local variables (like a "var" statement).
// The code generator needs to track ownership of such variables, so it
// requires them not to have incomplete types.

// For match terms, this rule is waived, because the match compiler uses
// "let" instead of "var" in this case, and ownership issues don't arise
// with "let". Similarly, in ghost code, ownership is not an issue, so the
// above rule doesn't apply for ghost code.

// Note: No separate rule is required for the scrutinee. The match compiler
// does convert non-lvalue scrutinees to "var" variables, so one might
// think a "no incomplete type" rule would be needed there as well; but
// non-lvalues can't ever have incomplete types (see e.g.
// ValuePosIncomplete.b), so in fact no rule is needed.

interface {}

function byvalue_pattern_var(ref r: i32[]): u64
{
    match r {
    case x => return sizeof(x);       // error: non-ref variable x with incomplete type
    }
}

function byvalue_field(ref p: {i32[], i32}): u64
{
    match p {
    case {x, _} => return sizeof(x);  // error: non-ref variable x with incomplete type
    }
}

function ref_pattern_var(ref r: i32[]): u64
{
    match r {
    case ref x => return sizeof(x);   // ok (x is "ref" not "var")
    }
}

function ref_field(ref p: {i32[], i32}): u64
{
    match p {
    case {ref x, _} => return sizeof(x);   // ok (x is "ref")
    }
}

function wildcard(ref r: i32[]): u64
{
    match r {                          // ok: no pattern variables
    case _ => return sizeof(r);
    }
}

function complete_field(ref p: {i32[], i32}): i32
{
    match p {
    case {_, n} => return n;           // ok: n has a complete type (the i32[] field is not bound)
    }
}

ghost function ghost_copies(c: bool, ref r: i32[], ref s: i32[]): u64
{
    match (if c then r else s) {       // ok: ghost code, above rule does not apply
    case x => return sizeof(x);
    }
}

function match_term(ref r: i32[], ref p: {i32[], i32}): u64
{
    // ok: match terms (not statements), so the above rule does not apply
    var n1 = match r { case x => sizeof(x) };
    var n2 = match p { case {x, _} => sizeof(x) };
    return n1;
}
