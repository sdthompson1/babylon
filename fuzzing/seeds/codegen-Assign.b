module Main

interface {
    function main();
}

import Test;

datatype Test = A | B(bool);

function get_bool(x: Test): bool
{
    return match x {
      case A => false
      case B(flag) => flag
    };
}

function main()
{
    var x = B(true);
    x = A;

    // In this next assignment statement, the compiler cannot simply start writing
    // the right-hand-side term into the memory occupied by x, because this will
    // first overwrite x's tag, changing x from A to B(true), then call get_bool(x),
    // which will then return the wrong value (true instead of false).
    // The codegen should instead compute the right-hand-side into a temporary memory
    // block, then "memcpy" that temp block into x.
    x = B(get_bool(x));
    
    assert x == B(false);

    match x {
    case B(false) => print_string("test passed\n");
    case _ => print_string("test failed\n");
    }
}
