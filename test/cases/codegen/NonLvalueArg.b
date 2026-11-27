module NonLvalueArg

// An argument that is not an lvalue is a value of its own: it does not share
// storage with any variable.
//
// Each function below takes a 'ref' argument and a by-value argument. It
// writes 5 through the 'ref' and then reads the by-value argument. A by-value
// argument is a copy of the value that the argument had at the call, so the
// function returns what was there before the write, namely 0. The verifier
// agrees: every 'assert' below is proved.
//
// The calls pass the same variable twice: once as the 'ref', and once inside
// a 'let', 'match' or 'if' expression. The aliasing rule does not object,
// because it only looks at arguments that are lvalues, and a 'let', 'match'
// or 'if' expression is not an lvalue. That is correct, provided that the
// compiler gives the result of such an expression storage of its own. If it
// passes the address of the variable instead, then the callee's write shows
// through the by-value argument, and the program prints 5 where the verifier
// proved 0.
//
// (The calls marked "shares" below are the ones that printed 5 from the C
// compiler when this test was written. The Isabelle compiler printed 5 at
// those of them that are written with 'let', and 0 at the 'match' ones.)

interface { function main(); }

import Test;

type P = {x: i32, y: i32};
type Q = {p: P, n: i32};
datatype M = Nope | Yes(i32);

function f(ref a: P, b: P): i32
    ensures return == b.x;
{
    a.x = 5;
    return b.x;
}

function f_field(ref a: Q, b: P): i32
    ensures return == b.x;
{
    a.p.x = 5;
    return b.x;
}

function f_elem(ref a: P[3], b: P): i32
    ensures return == b.x;
{
    a[1].x = 5;
    return b.x;
}

function f_array(ref a: i32[3], b: i32[3]): i32
    ensures return == b[0];
{
    a[0] = 5;
    return b[0];
}

function f_incomplete(ref a: i32[3], b: i32[]): i32
    requires sizeof(b) == u64(3);
    ensures return == b[0];
{
    a[0] = 5;
    return b[0];
}

function main()
{
    var c: bool = true;
    var m: M = Yes(1);
    var r: {i32, i32} = {1, 2};


    // 'let' expressions

    var p: P = {x = 0, y = 0};

    var v1 = f(p, let n = 1 in p);                    // shares
    assert v1 == 0;
    print_i32(v1);
    p.x = 0;

    var v2 = f(p, let q = p in q);                    // shares
    assert v2 == 0;
    print_i32(v2);
    p.x = 0;

    var v3 = f(p, let n = 1 in let k = 2 in p);       // shares
    assert v3 == 0;
    print_i32(v3);
    p.x = 0;


    // 'match' expressions that need no test. (The match compiler turns
    // these into 'let' expressions.)

    var v4 = f(p, match c { case _ => p });           // shares
    assert v4 == 0;
    print_i32(v4);
    p.x = 0;

    var v5 = f(p, match true { case _ => p });        // shares
    assert v5 == 0;
    print_i32(v5);
    p.x = 0;

    var v6 = f(p, match p { case q => q });           // shares
    assert v6 == 0;
    print_i32(v6);
    p.x = 0;

    var v7 = f(p, match r { case {_, _} => p });      // shares
    assert v7 == 0;
    print_i32(v7);
    p.x = 0;


    // 'match' and 'if' expressions that do need a test

    var v8 = f(p, match c { case true => p  case false => p });
    assert v8 == 0;
    print_i32(v8);
    p.x = 0;

    var v9 = f(p, if c then p else p);
    assert v9 == 0;
    print_i32(v9);
    p.x = 0;

    var v10 = f(p, match m { case Yes(_) => p  case Nope => p });
    assert v10 == 0;
    print_i32(v10);
    p.x = 0;

    var v11 = f(p, match m { case Yes(k) => p  case Nope => p });
    assert v11 == 0;
    print_i32(v11);
    p.x = 0;


    // A field or an element of the result, in either order

    var q: Q = {p = {x = 0, y = 0}, n = 0};

    var w1 = f_field(q, (let n = 1 in q).p);          // shares
    assert w1 == 0;
    print_i32(w1);
    q.p.x = 0;

    var w2 = f_field(q, let n = 1 in q.p);            // shares
    assert w2 == 0;
    print_i32(w2);
    q.p.x = 0;

    var w3 = f_field(q, (match c { case _ => q }).p); // shares
    assert w3 == 0;
    print_i32(w3);
    q.p.x = 0;

    var ps: P[3];

    var u1 = f_elem(ps, (let n = 1 in ps)[1]);        // shares
    assert u1 == 0;
    print_i32(u1);
    ps[1].x = 0;

    var u2 = f_elem(ps, let n = 1 in ps[1]);          // shares
    assert u2 == 0;
    print_i32(u2);
    ps[1].x = 0;


    // Arrays. In the last call the result of the 'let' is converted to
    // i32[], so the callee gets a view of the temporary, not of 'xs'.

    var xs: i32[3];

    var t1 = f_array(xs, let n = 1 in xs);            // shares
    assert t1 == 0;
    print_i32(t1);
    xs[0] = 0;

    var t2 = f_array(xs, match c { case _ => xs });   // shares
    assert t2 == 0;
    print_i32(t2);
    xs[0] = 0;

    var t3 = f_incomplete(xs, let n = 1 in xs);       // shares
    assert t3 == 0;
    print_i32(t3);
    xs[0] = 0;
}
