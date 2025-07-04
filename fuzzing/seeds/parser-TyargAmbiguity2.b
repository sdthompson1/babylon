module TyargAmbiguity2

import Test;

interface {
    function foo(x: i32): bool
    {
        // Here "< {" looks like it might be introducing a type argument
        // list followed by a record type, but when we get to the "100"
        // this cannot be the case, so backtracking occurs.
        return (x < {100}.0);
    }

    function main()
    {
        Test.print_bool(foo(0));
        Test.print_bool(foo(999));
    }
}
