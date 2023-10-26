module GhostFunc
interface {

    // Regression test.

    const FRAC_BITS = 20;

    ghost function num_bits(x: i32, n: i32): bool
        requires 0 <= n <= 30 - FRAC_BITS;
    {
        var limit: i32 = (1 << (FRAC_BITS + n));
        var b1 = -limit < x;
        var b2 = x < limit;
        return b1 && b2;
    }

    ghost function test()
    {
        assert (num_bits(1, 5));
    }

    function main()
    {}

}
