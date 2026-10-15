module RecursiveFunction

interface {
    function sum_upto(n: u32): u32;
}

// Try to define a recursive function. Babylon does not support recursive
// functions currently, so this is an error.
function sum_upto(n: u32): u32
{
    if n == 0 {
        return 0;
    } else {
        return n + sum_upto(n - 1);
    }
}
