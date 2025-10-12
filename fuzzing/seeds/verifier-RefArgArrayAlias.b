module Main
interface {}

function foo(ref x: i32, ref y: i32)
{
}

function test1(ref a: i32[])
    requires sizeof(a) > u64(10);
{
    foo(a[0], a[1]);    // OK
    foo(a[0], a[0]);    // Error, may alias
}

function test2(ref x: {a: i32[*], b: i32[*]}, i: u32, j: u32)
    requires sizeof(x.a) > u64(10);
    requires sizeof(x.b) > u64(10);
    requires i < 10;
    requires j < 10;
    requires i != j;
{
    foo(x.a[0], x.b[0]);    // OK
    foo(x.a[i], x.a[j]);    // OK because i != j
    foo(x.a[i], x.a[0]);    // Error because i might be 0
}

