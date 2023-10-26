module TyargAmbiguity
import Test;

interface {

    const M = 100;

    function foo(x: i32, y: i32): bool
    {
        // The "<" here should be interpreted as less-than,
        // rather than introducing a type argument list.
        return (-M < x < M) && (-M < y < M);
    }

    function main()
    {
        Test.print_bool(foo(0,10));
        Test.print_bool(foo(1000,20));
    }
}
