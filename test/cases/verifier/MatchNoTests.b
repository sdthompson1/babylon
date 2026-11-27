module MatchNoTests

// A "trivial" match (one that needs no test), such as `match c { case _ => p }`,
// must still be treated as a match expression by the verifier -- i.e. it must
// not be simplified down to its body, "p", even though this might seem like a
// reasonable thing to do:
//
//  - `match c { case _ => p }` is not an lvalue, so it never aliases anything;
//    but `p` is an lvalue, so it could trigger an aliasing violation.
//
//  - The `p` in `match c { case _ => p }` is in a value position, so it cannot
//    be allocated in executable code; if the expression was reduced to `p` then
//    this check might be skipped (if the match itself was in a place position).
//
// See also ValuePosAlloc.b and codegen/NonLvalueArg.b.

interface {}

import Test;

type P = {x: i32, y: i32};

function f(ref a: P, b: P): i32
    ensures return == b.x;
{
    a.x = 5;
    return b.x;
}

function alloc_size(a: i32[*]): u64
{
    return sizeof(a);
}


// ---------------------------------------------------------------------
// Aliasing

function alias_direct(ref p: P): i32
{
    return f(p, p);                                   // Error, aliasing
}

function alias_wildcard(c: bool, ref p: P): i32
{
    return f(p, match c { case _ => p });             // OK
}

function alias_record_pattern(r: {i32, i32}, ref p: P): i32
{
    return f(p, match r { case {_, _} => p });        // OK
}

function alias_nested(c: bool, ref p: P): i32
{
    return f(p, match c { case _ => match c { case _ => p } });    // OK
}

function alias_field(c: bool, ref q: {p: P, n: i32}): i32
{
    return f(q.p, (match c { case _ => q }).p);       // OK
}


// Other forms, for comparison.
function alias_other_forms(c: bool, ref p: P): i32
{
    var v1 = f(p, match true { case _ => p });        // OK
    var v2 = f(p, match p { case q => q });           // OK
    var v3 = f(p, match c { case true => p  case false => p });    // OK
    var v4 = f(p, let n = 1 in p);                    // OK
    return v1;
}

function result_is_a_copy(c: bool, ref p: P)
    requires p.x == 0;
{
    var v = f(p, match c { case _ => p });
    assert v == 0;                                    // OK
    assert p.x == 0;                                  // Error, f might have changed p
}


// ---------------------------------------------------------------------
// Value positions

function arm_allocated(c: bool, ref a: i32[*]): u64
{
    return alloc_size(match c { case _ => a });       // Error, a might be allocated
}

function arm_allocated_record_pattern(r: {i32, i32}, ref a: i32[*]): u64
{
    return alloc_size(match r { case {_, _} => a });  // Error, a might be allocated
}

function arm_allocated_index(c: bool, ref a: i32[*]): i32
    requires sizeof(a) > u64(0);
{
    return (match c { case _ => a })[0];              // Error, a might be allocated
}

function arm_not_allocated(c: bool, ref a: i32[*]): u64
    requires !allocated(a);
{
    return alloc_size(match c { case _ => a });       // OK
}

function arm_scalar(c: bool, ref a: i32[*]): u64
{
    return match c { case _ => sizeof(a) };           // OK, a is not copied
}

// The scrutinee is a place position, whatever the patterns are.
function scrutinee_allocated(ref a: i32[*]): i32
{
    return match a { case _ => 1 };                   // OK
}

ghost function ghost_arm(c: bool, a: i32[*]): u64
{
    return alloc_size(match c { case _ => a });       // OK, ghost code
}
