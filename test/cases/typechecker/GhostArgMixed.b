module GhostArgMixed
interface {}

function complex(
    ref x: i32,
    ghost y: bool,
    ghost ref z: i32,
    w: u8
): i32
{
    x = x + 1;
    ghost z = z + i32(w);
    return x + i32(w);
}

function test()
{
    var a = 10;
    var b = 20;
    ghost var c = 30;

    var result = complex(a, true, c, u8(5));  // OK
    var bad = complex(a, true, a, u8(5));     // Error: ref ghost needs ghost lvalue
}
