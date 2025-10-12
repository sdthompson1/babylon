module Main

interface {}

function foo(x: i32, y: i32, ref r: i32)
{
}

function bar(ref r: i32, ref s: i32, x: i32)
{
}

function f1()
{
    var a = 1;
    var b = 2;
    var c = 3;

    foo(a, b, c);    // ok, no aliasing
    foo(a, a, c);    // ok, 2 normal args are allowed to alias
    foo(a, b, b);    // error, normal arg cannot alias ref
    foo(a, b, a);    // error, normal arg cannot alias ref

    bar(a, a, 100);     // Error, two ref args alias

    var z: {i32,i32};
    bar(z.0, z.1, 100);  // OK
    bar(z.0, z.0, 100);  // Error, two ref args alias
}

function f2()
{
    var a: i32 = 0;
    ref r = a;
    bar(a, r, 0);    // Error, 'a' and 'r' alias
}

datatype Mytype = I32(i32) | Bool(bool);

function baz(ref x: i32, ref y: Mytype)
{
}

function f3()
{
    var v = I32(1);
    match v {
    case I32(ref r) =>
        baz(r, v);  // Error: r aliases (part of) v
    }
}

function string_arg(ref x: u8[], y: u8[])
{
}

function f4(ref a: u8[])
{
    string_arg(a, "hello");  // ok
    string_arg(a, a);   // error
}
