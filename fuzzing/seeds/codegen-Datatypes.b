module Main

// Some codegen tests for datatypes

interface { function main(); }

import Test;


datatype Color = Red | Green | Blue;

function f1(c: Color): Color
{
    return Blue;
}


datatype Multi<a,b> = M1 {a,a,b} | M2 {b,a,b} | M3;

function f2<a,b>(m: Multi<a,b>): Multi<a,b>
    requires !allocated(m);
{
    var m_copy: Multi<a,b> = m;
    return m_copy;
}

function f3<a>(m: Multi<i32,a>): Multi<i16,i8>
{
    var c2: Multi<bool,i64> = f2<bool,i64>(M3<bool,i64>);
    var test_var = c2;
    var test_col = Red;
    test_col = Green;
    return M3<i16,i8>;
}

function foo()
{
    var c3: Multi<i16,i8> = f3<u16>(M3<i32,u16>);
}


//
// Default init of datatypes
//

function default_init_1()
{
    var c: Color;
    c = Red;
}

function default_init_2<a>()
    requires !allocated(default<a>());
{
    var x: a;
}


//
// Initialising and copying fields
//

function fields_1()
{
    var m1: Multi<i32, bool> = M1<i32, bool> { 100, 33+66, true };
    var m2: Multi<i32, bool> = M3<i32, bool>;
    var m3: Multi<i32, bool>;
    m1 = m2;
    m1 = M2<i32, bool> { false, 99, true };
    m2 = m1;

    var m4: Multi<Multi<i32,i32>, bool> = M2<Multi<i32,i32>, bool> { true, M3<i32,i32>, false };
    var m5: Multi<Multi<i32,i32>, bool> = M2<Multi<i32,i32>, bool> { true, M3<i32,i32>, true };
    m4 = m5;
}

function fields_2<a,b>(x: a, y: b): Multi<Multi<a,b>, i32>
    requires !allocated(default<Multi<a,b> >());
    requires !allocated(x);
    requires !allocated(y);
{
    var m1: Multi<a, b>;
    var m2: Multi<a, b> = M1<a, b> { x, x, y };
    m2 = m1;

    var m4: Multi<Multi<a,b>, i32> = M1<Multi<a,b>, i32> { m1, m2, 1000 };

    return m4;
}


datatype D<a,b> = D1 { x: a, y: b } | D2 { p: b, q: a } | D3 { x: a };

const myconst =
    D1< D<i8,i16>, i32 > {
        // Note p and q have to be in the right order,
        // as {p:i16,q:i8} and {q:i8,p:i16} are considered different types currently.
        // Also, we need the explicit casts, as otherwise we get the type
        // {p:i32,q:i32} and it won't implicitly cast fields within records.
        x = D2<i8,i16> { p=i16(2222), q=i8(11) },
        y = 1234567
    };
    

function main()
{
    foo();
    Test.print_i16( match (myconst) { case D1{x=D2{p=value}} => value } );
    Test.print_i8 ( match (myconst) { case D1{x=D2{q=value}} => value } );
    Test.print_i32( match (myconst) { case D1{y=value} => value } );
}
