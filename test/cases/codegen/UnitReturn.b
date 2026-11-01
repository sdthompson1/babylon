module UnitReturn

// Functions returning the unit type {} are compiled to void C functions
// (with no "ret" parameter), exactly like procedures.

interface {
    function main();
}

import Test;

function f(): {}
{
    print_string("f\n");
    return {};
}

function g(): {}
{
    print_string("g\n");
    return f();   // a unit-typed call in a return statement
}

function h(b: bool): {}
{
    print_string("h\n");
    return if b then f() else g();   // a non-call unit-typed term with side effects
}

function k(x: {}): {}
{
    print_string("k\n");
    return x;
}

function main()
{
    var x: {} = g();        // call as an expression
    x = h(true);
    match k(x) {            // call as a match scrutinee
    case {} =>
        print_string("done\n");
    }
    x = print_string_unit("extern\n");   // extern function returning {}
}
