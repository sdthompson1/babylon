// "Wrapping" integer arithmetic (i.e. arithmetic modulo 2^n, where
// n = 8, 16, 32 or 64).

// Note that, for now, we provide this for the unsigned types only.

// [NOTE: Perhaps we should add "wrapping" operators (&+, &-, etc.)
// to the language itself, like in Swift for example. If that was
// done, then this file would be unnecessary.]


module IntWrap

import Int;
import IntDivision;

interface {

    // u8 operations

    function u8_wrap_add(x: u8, y: u8): u8
        ensures int(return) == int_mod(int(x) + int(y), int(U8_MAX) + int(1));

    function u8_wrap_sub(x: u8, y: u8): u8
        ensures int(return) == int_mod(int(x) - int(y), int(U8_MAX) + int(1));

    function u8_wrap_mul(x: u8, y: u8): u8
        ensures int(return) == int_mod(int(x) * int(y), int(U8_MAX) + int(1));

    // Note: "wrapped division" is not provided, because it is equivalent
    // to normal division ("/" operator).


    // u16 operations

    function u16_wrap_add(x: u16, y: u16): u16
        ensures int(return) == int_mod(int(x) + int(y), int(U16_MAX) + int(1));

    function u16_wrap_sub(x: u16, y: u16): u16
        ensures int(return) == int_mod(int(x) - int(y), int(U16_MAX) + int(1));

    function u16_wrap_mul(x: u16, y: u16): u16
        ensures int(return) == int_mod(int(x) * int(y), int(U16_MAX) + int(1));


    // u32 operations

    function u32_wrap_add(x: u32, y: u32): u32
        ensures int(return) == int_mod(int(x) + int(y), int(U32_MAX) + int(1));

    function u32_wrap_sub(x: u32, y: u32): u32
        ensures int(return) == int_mod(int(x) - int(y), int(U32_MAX) + int(1));

    function u32_wrap_mul(x: u32, y: u32): u32
        ensures int(return) == int_mod(int(x) * int(y), int(U32_MAX) + int(1));


    // u64 operations

    function u64_wrap_add(x: u64, y: u64): u64
        ensures int(return) == int_mod(int(x) + int(y), int(U64_MAX) + int(1));

    function u64_wrap_sub(x: u64, y: u64): u64
        ensures int(return) == int_mod(int(x) - int(y), int(U64_MAX) + int(1));

    function u64_wrap_mul(x: u64, y: u64): u64
        ensures int(return) == int_mod(int(x) * int(y), int(U64_MAX) + int(1));

}


// Implementation:

function u8_wrap_add(x: u8, y: u8): u8
    ensures int(return) == int_mod(int(x) + int(y), int(U8_MAX) + int(1));
{
    return (u16(x) + u16(y)) % (u16(U8_MAX) + u16(1));
}

function u8_wrap_sub(x: u8, y: u8): u8
    ensures int(return) == int_mod(int(x) - int(y), int(U8_MAX) + int(1));
{
    return (u16(U8_MAX) + u16(1) + x - y) % (u16(U8_MAX) + u16(1));
}

function u8_wrap_mul(x: u8, y: u8): u8
    ensures int(return) == int_mod(int(x) * int(y), int(U8_MAX) + int(1));
{
    return (u16(x) * u16(y)) % (u16(U8_MAX) + u16(1));
}

function u16_wrap_add(x: u16, y: u16): u16
    ensures int(return) == int_mod(int(x) + int(y), int(U16_MAX) + int(1));
{
    return (u32(x) + u32(y)) % (u32(U16_MAX) + u32(1));
}

function u16_wrap_sub(x: u16, y: u16): u16
    ensures int(return) == int_mod(int(x) - int(y), int(U16_MAX) + int(1));
{
    return (u32(U16_MAX) + u32(1) + x - y) % (u32(U16_MAX) + u32(1));
}

function u16_wrap_mul(x: u16, y: u16): u16
    ensures int(return) == int_mod(int(x) * int(y), int(U16_MAX) + int(1));
{
    return (u32(x) * u32(y)) % (u32(U16_MAX) + u32(1));
}

function u32_wrap_add(x: u32, y: u32): u32
    ensures int(return) == int_mod(int(x) + int(y), int(U32_MAX) + int(1));
{
    return (u64(x) + u64(y)) % (u64(U32_MAX) + u64(1));
}

function u32_wrap_sub(x: u32, y: u32): u32
    ensures int(return) == int_mod(int(x) - int(y), int(U32_MAX) + int(1));
{
    return (u64(U32_MAX) + u64(1) + x - y) % (u64(U32_MAX) + u64(1));
}

function u32_wrap_mul(x: u32, y: u32): u32
    ensures int(return) == int_mod(int(x) * int(y), int(U32_MAX) + int(1));
{
    return (u64(x) * u64(y)) % (u64(U32_MAX) + u64(1));
}

function u64_wrap_add(x: u64, y: u64): u64
    ensures int(return) == int_mod(int(x) + int(y), int(U64_MAX) + int(1));
{
    var xx: u64 = x;
    var yy: u64 = y;
    var c: u64 = 0;

    var m: u64 = u64(1) << 63;

    if xx >= m {
        xx = xx - m;
        c = m;
    }

    assert int(x) + int(y) == int(xx) + int(yy) + int(c);

    if yy >= m {
        yy = yy - m;
        c = m - c;
    }

    assert int(x) + int(y) == int(xx) + int(yy) + int(c)
        || int(x) + int(y) == int(xx) + int(yy) + int(c) + int(U64_MAX) + int(1);

    if xx + yy >= m {
        return xx + yy - c;
    } else {
        return xx + yy + c;
    }
}

function u64_wrap_sub(x: u64, y: u64): u64
    ensures int(return) == int_mod(int(x) - int(y), int(U64_MAX) + int(1));
{
    if x < y {
        return ~(y - x) + 1;
    } else {
        return x - y;
    }
}


// For u64_wrap_mul:

// Our strategy here is to split x and y into two 32-bit "halves", then
// do a series of 32 * 32 -> 64 bit multiplies to get the result we need.

// First, we prove some lemmas.

// This multiplies out (xh * M + xl) * (yh * M + yl).
ghost function mul_split_lemma(x: int, y: int,
                               xh: int, xl: int,
                               yh: int, yl: int,
                               M: int)
    requires x == xh * M + xl;
    requires y == yh * M + yl;
    ensures x * y == xh * yh * (M*M) + (xh * yl + xl * yh) * M + xl * yl;
{}

// Reducing (a * M) mod (M*M)
ghost function mod_lemma_1(a: int, M: int)
    requires M > int(0);
    ensures int_mod(a * M, M*M) == int_mod(a, M) * M;
{
    var r1 = int_mod(a, M);
    obtain (q1: int) a == q1 * M + r1;
    mod_unique(a * M, M * M, q1, r1 * M);
}

// Reducing (a + b * M) mod (M*M)
ghost function mod_lemma_2(a: int, b: int, M: int)
    requires M > int(0);
    ensures int_mod(a + b * M, M*M) == int_mod(a + int_mod(b, M) * M, M*M);
{
    hide int_mod;

    assert int_mod(b * M, M*M) == int_mod(b, M) * M
    {
        mod_lemma_1(b, M);
    }

    assert int_mod(a + b * M, M*M)
        == int_mod(a + int_mod(b, M) * M, M*M)
    {
        mod_add(b * M, a, M*M);
    }
}

// Reducing (a * M*M + (b + c) * M + d) mod (M*M)
ghost function mod_lemma_3(a: int, b: int, c: int, d: int, M: int)
    requires M > int(0);
    ensures int_mod(a * M*M + (b + c) * M + d, M*M)
        == int_mod( int_mod(d + int_mod(c,M)*M, M*M)
                      + int_mod(b,M)*M,
                    M*M);
{
    assert int_mod(a * M*M + (b + c) * M + d, M*M)
        == int_mod((b + c) * M + d, M*M)
    {
        mod_add(a * M*M, (b + c) * M + d, M*M);
        mod_zero(a, M*M);
    }
    
    assert int_mod((b + c) * M + d, M*M)
        == int_mod(int_mod(d + c * M, M*M) + b * M, M*M)
    {
        mod_add(d + c * M, b * M, M*M);
    }
    
    assert int_mod(int_mod(d + c * M, M*M) + b * M, M*M)
        == int_mod(int_mod(d + c * M, M*M) + int_mod(b, M) * M, M*M)
    {
        mod_lemma_2(int_mod(d + c * M, M*M), b, M);
    }
    
    assert int_mod(d + c * M, M*M)
        == int_mod(d + int_mod(c,M) * M, M*M)
    {
        mod_lemma_2(d, c, M);
    }
}

// Apparently this is needed...!
ghost function u64_non_neg(x: u64)
    ensures x >= 0;
{}

// Now for our implementation of u64_wrap_mul.
function u64_wrap_mul(x: u64, y: u64): u64
    ensures int(return) == int_mod(int(x) * int(y), int(U64_MAX) + int(1));
{
    var TWO_TO_32: u64 = u64(U32_MAX) + 1;
    ghost var M: int = int(TWO_TO_32);

    // Split inputs into high and low halves.
    var xh = x / TWO_TO_32;
    var xl = x % TWO_TO_32;
    var yh = y / TWO_TO_32;
    var yl = y % TWO_TO_32;

    ghost int_mod_is_percent(int(x), M);
    ghost int_mod_is_percent(int(y), M);

    // Prove that x*y == (xh*yh)*(2**64) + (xh*yl + xl*yh)*(2**32) + xl*yl.
    ghost mul_split_lemma(int(x), int(y), int(xh), int(xl), int(yh), int(yl), M);

    // Calculate partial products.
    ghost var hi_hi: u64 = xh * yh;
    var hi_lo: u64 = xh * yl;
    var lo_hi: u64 = xl * yh;
    var lo_lo: u64 = xl * yl;

    // Calculate low 64-bit half of the 128-bit product.
    var z: u64 = u64_wrap_add(lo_lo, (lo_hi % TWO_TO_32) * TWO_TO_32);
    var result: u64 = u64_wrap_add(z, (hi_lo % TWO_TO_32) * TWO_TO_32);

    ghost u64_non_neg(hi_lo);
    ghost u64_non_neg(lo_hi);
    ghost int_mod_is_percent(int(hi_lo), M);
    ghost int_mod_is_percent(int(lo_hi), M);

    // Prove the postcondition.
    ghost mod_lemma_3(int(hi_hi), int(hi_lo), int(lo_hi), int(lo_lo), int(TWO_TO_32));

    // Return the low 64-bit half of the product.
    return result;
}
