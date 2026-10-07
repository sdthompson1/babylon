module GhostExtern

interface {}

// A ghost extern function acts as an unproven axiom.

ghost function pow(x: int, n: int): int
    requires n >= int(0);
{
    var r: int = int(1);
    var i: int = int(0);
    while i < n
        invariant int(0) <= i <= n;
        decreases n - i;
    {
        r = r * x;
        i = i + int(1);
    }
    return r;
}

ghost extern function fermat(x: int, y: int, z: int, n: int)
    requires x > int(0) && y > int(0) && z > int(0);
    requires n > int(2);
    ensures pow(x,n) + pow(y,n) != pow(z,n);

ghost function test1(a: int, b: int, c: int)
    requires a > int(0) && b > int(0) && c > int(0);
{
    fermat(a, b, c, int(5));
    assert pow(a,int(5)) + pow(b,int(5)) != pow(c,int(5));     // OK, follows from the axiom
}

ghost function test2(a: int, b: int, c: int)
    requires a > int(0) && b > int(0) && c > int(0);
{
    assert pow(a,int(5)) + pow(b,int(5)) != pow(c,int(5));     // Fails, axiom not invoked
}

ghost function test3(a: int, b: int, c: int)
{
    fermat(a, b, c, int(5));     // Fails, precondition not met
}

function test4(a: i32, b: i32, c: i32)
    requires a > 0 && b > 0 && c > 0;
{
    ghost fermat(int(a), int(b), int(c), int(3));    // OK, ghost call from executable code
    assert pow(int(a),int(3)) + pow(int(b),int(3)) != pow(int(c),int(3));   // OK
}
