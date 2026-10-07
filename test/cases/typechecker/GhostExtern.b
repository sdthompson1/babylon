module GhostExtern

interface {
    ghost extern function in_interface(x: int): int;   // OK
}

ghost extern function axiom1(x: int)       // OK
    requires x > int(0);
    ensures x * x > int(0);

extern ghost function axiom2(): bool;      // OK, keywords in either order

ghost extern function named() = "foo";     // Error, ghost extern cannot have an extern name

ghost extern function with_body() { }      // Error, extern function cannot have a body

ghost function use_ghost_externs()
{
    axiom1(int(5));                   // OK
    var b = axiom2();                 // OK
    var y = in_interface(int(1));     // OK
}

function use_from_executable(): i32
{
    ghost axiom1(int(5));             // OK, ghost call statement
    var b = axiom2();                 // Error, can't call ghost function from executable code
    return 0;
}
