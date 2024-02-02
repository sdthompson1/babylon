module ShortCircuit

import Test;

interface {
    function main();
}

type Tuple = {i32,i32};

datatype A = A | B;

function main()
{
    var arr: Tuple[10];

    // This checks that the "wrong" branch of an if-then-else expr is NOT
    // evaluated if the condition is false.
    var t = if false then arr[99999999] else arr[0];
    print_i32(t.0);

    // Similarly for &&, ||
    print_bool(false && arr[99999999].0 == 0);
    print_bool(true || arr[99999999].0 == 0);

    // Similarly for match
    var x: {i32} = match B { 
        case A => {arr[99999999].0}
        case B => {arr[0].0}
    };
    print_i32(x.0);
}
