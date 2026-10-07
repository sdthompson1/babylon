module GhostArgInfer

// Tests for type inference at calls that have ghost arguments.
//
// In an executable call, a ghost argument is type-checked against the
// call's type arguments but never determines them. The type arguments
// must be fixed by the non-ghost arguments, by the surrounding
// statement, or by writing them explicitly.
//
// Inside ghost code, ghost arguments can determine type arguments as
// usual.

interface {}

datatype Maybe<a> = Nothing | Just(a);

ghost function h<U>(): U
{
    var u: U;
    return u;
}

function h2<U>(): U
{
    var u: U;
    return u;
}

// The type parameter U is "phantom" (it does not appear in the
// argument or return types).
function p<U>(): bool
{
    return true;
}

function f1<T>(ghost z: T) {}
function f2<T>(x: T, ghost z: T) {}
function f3<T>(ghost y: Maybe<T>, ghost z: Maybe<T>) {}
function f4<T>(ghost y: Maybe<T>): Maybe<T> { return Nothing; }
function f5<T>(ghost y: Maybe<T>, ghost z: T) {}
function f6<T>(ref x: T, ghost ref z: T) {}
function f7<T>(ghost z: T, x: T) {}
function k(ghost z: int) {}
function kb(ghost b: bool) {}

function test_ghost_arg_alone()
{
    ghost var g: i32 = 1;
    ghost var n: int = int(1);
    f1(g);                  // error: T cannot be inferred from a ghost argument
    f1(n);                  // error: same (also, T := int would not be a runtime type)
    f3(Nothing, Just(g));   // error: same (reported at Just(g))
    f5(h(), n);             // error: same (U := Maybe<T> is fine, but then n does not match T)
    f1(h());                // error: unable to infer type (U := T, but T is never resolved)
}

function test_nonghost_arg_fixes_type()
{
    ghost var g: i32 = 1;
    var v: i32 = 2;
    var b: bool = true;
    f2(v, g);               // ok: T := i32 from v
    f2(v, b);               // error: type mismatch (T is i32, but b is bool)
    f6(v, g);               // ok: T := i32 from v; ghost ref gets a ghost lvalue
    f6(v, v);               // error: ghost ref argument requires a ghost lvalue

    // The non-ghost arguments are matched first, then the ghost ones,
    // regardless of the order they appear in. So T is fixed by v before
    // g is checked, even though g comes first.
    f7(g, v);               // ok: T := i32 from v
    f7(b, v);               // error: type mismatch (T is i32, but b is bool)
}

function test_statement_fixes_type()
{
    ghost var g: i32 = 1;
    var m: Maybe<i32> = f4(Nothing);    // ok: T := i32 from the declared type
    var m2: Maybe<i32> = f4(Just(g));   // error: T is still unknown when Just(g) is checked
    ghost f1(g);                        // ok: ghost statement, so the call is ghost code
}

function test_explicit_type_args()
{
    ghost var g: i32 = 1;
    ghost var n: int = int(1);
    f1<i32>(g);                 // ok
    f3<i32>(Nothing, Just(g));  // ok
    f5<i32>(h(), g);            // ok: U := Maybe<i32>
    f1<int>(g);                 // error: type argument must be a runtime type
}

function test_leftover_ghost_univar()
{
    k(h());                 // ok: U := int (inferred in ghost mode)
    kb(p());                // error: unable to infer type (U of p is never resolved)
    var v = h2();           // error: unable to infer type
}

ghost function test_ghost_context()
{
    var g: i32 = 1;
    var n: int = int(1);
    f1(g);                  // ok: in ghost code, ghost arguments can determine T
    f1(n);                  // ok
    f3(Nothing, Just(g));   // ok
    f5(h(), n);             // ok
}
