module Main

// Regression test for previously unsound behaviour of "type T
// (allocated_always);" (now fixed).

interface {
    function main();
}

import Imported;
import Test;

function main()
{
    // If T is declared as "type T (allocated_always);", this means
    // that allocated(x) can neither be proven nor disproven, for
    // any value x of type T.

    // If instead the rule was that allocated(x) is always true, for
    // all x of type T, that would be unsound, as the following test
    // demonstrates.

    var m: MaybeT;
    MakeT(m);

    match m {
    case Just(ref x) =>
        // Here, x has type T.
        
        // If the rule was that allocated(x) is true for all x of type
        // T, then we would be allowed to call Bad(x), which would be
        // unsound.

        // However, the actual rule is that allocated(x) is *unknown*
        // for all x of type T, and therefore, the below call is a
        // verifier error (can't prove precondition).

        Bad(x);
    }

    FreeT(m);
}
