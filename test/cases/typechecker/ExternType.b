module ExternType

interface {}

extern type Bad<a>;             // type variables can't be used with an abstract type

extern type Good: Default+Copy;

extern function use_good(x: Good): Good;

function f1(): Good
{
    var g1: Good;   // can default-construct
    var g2: Good = use_good(g1);  // can pass as arg, and get result
    return g2;      // can return from function
}

function f2(): Good
{
    var g: Good;
    g = g * 2;    // trying to multiply won't work
}
