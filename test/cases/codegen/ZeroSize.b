module ZeroSize

interface {
    function main();
}

import Test;

function f(x: {})
{
    match x {
    case {} =>
        print_string("Hello\n");
    }
}

function main()
{
    var x: {} = {};
    match x {
    case {} =>
        f(x);
    }
    x = {};
}
