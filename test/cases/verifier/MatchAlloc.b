module MatchAlloc

// In a match *statement*, a non-ref pattern variable is a copy of part of
// the scrutinee, so (in executable code) it must not bind a value that
// might be allocated.

// In a match *expression*, nothing is copied, so the restriction does
// not apply.

interface {}

datatype Maybe<a> = Nothing | Just(a);

function stmt_by_value(ref m: Maybe<i32[*]>): u64
{
    match m {
    case Just(a) => return sizeof(a);   // Error, copying from (possibly) allocated value
    case Nothing => return u64(0);
    }
}

function stmt_by_value_not_allocated(ref m: Maybe<i32[*]>): u64
    requires !allocated(m);
{
    match m {
    case Just(a) => return sizeof(a);   // OK, known to be non-allocated
    case Nothing => return u64(0);
    }
}

function stmt_by_ref(ref m: Maybe<i32[*]>): u64
{
    match m {
    case Just(ref a) => return sizeof(a);   // OK, no copy
    case Nothing => return u64(0);
    }
}

ghost function stmt_ghost(m: Maybe<i32[*]>): u64
{
    match m {
    case Just(a) => return sizeof(a);   // OK, ghost code
    case Nothing => return u64(0);
    }
}

function expr_by_value(ref m: Maybe<i32[*]>): u64
{
    return match m { case Just(a) => sizeof(a) case Nothing => u64(0) };   // OK, no copy
}

function expr_whole_scrutinee(ref a: i32[*]): u64
{
    return match a { case x => sizeof(x) };   // OK, no copy
}
