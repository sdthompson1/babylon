module Main

interface {}

// A case where we have ambiguity between an imported module
// and a function-local variable. In this case the local variable
// should shadow the module, because it is in an inner scope.

import qualified Foo as F;

function main()
{
    var F: {x:i32} = {x=10};
    assert F.x == 10;   // Valid (refers to F.x=10; Foo.x=100 is shadowed)
    assert F.z == 300;  // Invalid (even though Foo.z exists, it is shadowed by the above
                        // record, which doesn't contain a z field)
}
