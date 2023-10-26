module Import

interface {
    function f1(): i8;
    function f2(ref x: i8);
    function f3(ref x: i8, ref y: i8): i8;
}

function f1(): i8
{
    return 10;
}

function f2(ref x: i8)
{}

function f3(ref x: i8, ref y: i8): i8
{
    return 10;
}
