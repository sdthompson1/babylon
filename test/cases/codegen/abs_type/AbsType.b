module AbsType

interface {
    type AbsType: Copy;

    function make_abs(): AbsType;

    function set_value(ref a: AbsType, x: i32);

    function get_value(a: AbsType): i32;
}

type AbsType = {bool, i32};

function make_abs(): AbsType
{
    return {false, 0};
}

function set_value(ref a: AbsType, x: i32)
{
    a.1 = x;
}

function get_value(a: AbsType): i32
{
    return a.1;
}
