module Main

interface {
    function main();
}

import Test;
import GhostAbs;

function main()
{
    // "Model" is never mentioned in executable code here, but it does
    // appear in the postcondition of "double", so the verifier (and the
    // code generator) must still cope with it.
    ghost var m: Model = model_of(21);
    print_i32(double(21));
}
