module IncompleteTyArg

// A type argument must always be a complete type, whether it is
// written explicitly or inferred, in both executable and ghost code.

// This test checks the errors that are generated when this rule is
// broken.

interface {}

import Test;

datatype Maybe<a> = Nothing | Just(a);

type Pair<a> = {a, a};

function my_swap<T>(ref x: T, ref y: T)
{
    swap x, y;
}

function my_assign<T>(ref x: T, y: T)
{
    x = y;
}

function same<T>(x: T, y: T)
{
}

function fresh<U>(): U
{
    var u: U;
    return u;
}

ghost function ghost_fresh<U>(): U
{
    var u: U;
    return u;
}

function takes_ref(ref x: i32[])
{
}

function over_incomplete<T>(ref d: T[], s: T[])
{
}


// ---------------------------------------------------------------------
// Explicit type arguments (executable code)

function explicit_exec(ref a: i32[*], ref b: i32[10], ref c: i32[], ref d: i32[])
{
    my_swap<i32[]>(a, b);       // error: incomplete type argument
    my_assign<i32[]>(a, b);     // error: incomplete type argument
    same<i32[]>(c, d);          // error: incomplete type argument
    var m = Just<i32[]>(c);     // error: incomplete type argument
}


// ---------------------------------------------------------------------
// Explicit type arguments (ghost code)

ghost function explicit_ghost(ref a: i32[*], ref b: i32[10], ref c: i32[], ref d: i32[])
{
    my_swap<i32[]>(a, b);       // error: incomplete type argument
    my_assign<i32[]>(a, b);     // error: incomplete type argument
    same<i32[]>(c, d);          // error: incomplete type argument
    var m = Just<i32[]>(c);     // error: incomplete type argument
}


// ---------------------------------------------------------------------
// Inferred type arguments (executable code)

function inferred_exec(ref c: i32[], ref d: i32[])
{
    my_swap(c, d);              // error: T inferred as i32[]
    my_assign(c, d);            // error: T inferred as i32[]
    same(c, d);                 // error: T inferred as i32[]
    var m = Just(c);            // error: a inferred as i32[]
}


// ---------------------------------------------------------------------
// Inferred type arguments (ghost code)

ghost function inferred_ghost(ref c: i32[], ref d: i32[])
{
    my_swap(c, d);              // error: T inferred as i32[]
    my_assign(c, d);            // error: T inferred as i32[]
    same(c, d);                 // error: T inferred as i32[]
    var m = Just(c);            // error: a inferred as i32[]
}


// ---------------------------------------------------------------------
// Type arguments in written types

function written_datatype(x: Maybe<i32[]>)    // error: incomplete type argument
{
}

function written_typedef(x: Pair<i32[]>)      // error: incomplete type argument
{
}

ghost function written_ghost(x: Maybe<i32[]>) // error: incomplete type argument
{
}


// ---------------------------------------------------------------------
// A match expression whose first arm's type is an uninferred type
// argument, and whose second arm has an incomplete type.

function match_infer_exec(c: bool, ref s: i32[]): u64
{
    return sizeof(match c { case true => fresh() case false => s });   // error: U inferred as i32[]
}

ghost function match_infer_ghost(c: bool, ref s: i32[]): u64
{
    return sizeof(match c { case true => ghost_fresh() case false => s });   // error: U inferred as i32[]
}


// ---------------------------------------------------------------------
// Still legal

function legal(c: bool, a: i32[], ref b: i32[10], ref r: i32[], ref s: i32[]): u64
    requires sizeof(r) > u64(0);
    requires sizeof(s) > u64(0);
{
    // by-value parameter of incomplete type (a) is fine

    // ref local of incomplete type
    ref r2 = r;

    // passing a fixed-size array to a ref T[] parameter
    takes_ref(b);

    // generic function declared over T[], instantiated at T := i32
    over_incomplete(r, a);
    over_incomplete<i32>(s, a);

    // if and match expressions of incomplete type
    var n1 = sizeof(if c then r else s);
    var n2 = sizeof(match c { case true => r case false => s });
    var x1 = (if c then r else s)[0];
    var x2 = (match c { case true => r case false => s })[0];

    // a ghost var of incomplete type is allowed
    ghost var saved = a;

    return n1 + n2;
}
