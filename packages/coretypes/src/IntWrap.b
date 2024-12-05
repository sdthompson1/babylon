// "Wrapping" integer arithmetic (i.e. arithmetic modulo 2^n, where
// n = 8, 16, 32 or 64).

// Note that, for now, we provide this for the unsigned types only.

// [NOTE: Perhaps we should add "wrapping" operators (&+, &-, etc.)
// to the language itself, like in Swift for example. If that was
// done, then this file would be unnecessary.]


module IntWrap

import Int;

interface {

    // u8 operations

    function u8_wrap_add(x: u8, y: u8): u8
        ensures int(return) == (int(x) + int(y)) % (int(U8_MAX) + int(1));

    function u8_wrap_sub(x: u8, y: u8): u8
        // Note: we could also use int_euclid_div to specify this
        // (which would avoid the awkward addition of U8_MAX + 1
        // on the lhs of the % operator), but doing it this way
        // makes this module more self-contained.
        ensures int(return) == (int(U8_MAX) + int(1) + int(x) - int(y)) % (int(U8_MAX) + int(1));

    function u8_wrap_mul(x: u8, y: u8): u8
        ensures int(return) == (int(x) * int(y)) % (int(U8_MAX) + int(1));

    // Note: "wrapped division" is not provided, because it is equivalent
    // to normal division ("/" operator).


    // u16 operations

    function u16_wrap_add(x: u16, y: u16): u16
        ensures int(return) == (int(x) + int(y)) % (int(U16_MAX) + int(1));

    function u16_wrap_sub(x: u16, y: u16): u16
        ensures int(return) == (int(U16_MAX) + int(1) + int(x) - int(y)) % (int(U16_MAX) + int(1));

    function u16_wrap_mul(x: u16, y: u16): u16
        ensures int(return) == (int(x) * int(y)) % (int(U16_MAX) + int(1));


    // u32 operations

    function u32_wrap_add(x: u32, y: u32): u32
        ensures int(return) == (int(x) + int(y)) % (int(U32_MAX) + int(1));

    function u32_wrap_sub(x: u32, y: u32): u32
        ensures int(return) == (int(U32_MAX) + int(1) + int(x) - int(y)) % (int(U32_MAX) + int(1));

    function u32_wrap_mul(x: u32, y: u32): u32
        ensures int(return) == (int(x) * int(y)) % (int(U32_MAX) + int(1));


    // u64 operations

    function u64_wrap_add(x: u64, y: u64): u64
        ensures int(return) == (int(x) + int(y)) % (int(U64_MAX) + int(1));

    function u64_wrap_sub(x: u64, y: u64): u64
        ensures int(return) == (int(U64_MAX) + int(1) + int(x) - int(y)) % (int(U64_MAX) + int(1));

    function u64_wrap_mul(x: u64, y: u64): u64
        ensures int(return) == (int(x) * int(y)) % (int(U64_MAX) + int(1));

}

// Implementation:

function u8_wrap_add(x: u8, y: u8): u8
    ensures int(return) == (int(x) + int(y)) % (int(U8_MAX) + int(1));
{
    return (u16(x) + u16(y)) % (u16(U8_MAX) + u16(1));
}

function u8_wrap_sub(x: u8, y: u8): u8
    ensures int(return) == (int(U8_MAX) + int(1) + int(x) - int(y)) % (int(U8_MAX) + int(1));
{
    return (u16(U8_MAX) + u16(1) + x - y) % (u16(U8_MAX) + u16(1));
}

function u8_wrap_mul(x: u8, y: u8): u8
    ensures int(return) == (int(x) * int(y)) % (int(U8_MAX) + int(1));
{
    return (u16(x) * u16(y)) % (u16(U8_MAX) + u16(1));
}

function u16_wrap_add(x: u16, y: u16): u16
    ensures int(return) == (int(x) + int(y)) % (int(U16_MAX) + int(1));
{
    return (u32(x) + u32(y)) % (u32(U16_MAX) + u32(1));
}

function u16_wrap_sub(x: u16, y: u16): u16
    ensures int(return) == (int(U16_MAX) + int(1) + int(x) - int(y)) % (int(U16_MAX) + int(1));
{
    return (u32(U16_MAX) + u32(1) + x - y) % (u32(U16_MAX) + u32(1));
}

function u16_wrap_mul(x: u16, y: u16): u16
    ensures int(return) == (int(x) * int(y)) % (int(U16_MAX) + int(1));
{
    return (u32(x) * u32(y)) % (u32(U16_MAX) + u32(1));
}

function u32_wrap_add(x: u32, y: u32): u32
    ensures int(return) == (int(x) + int(y)) % (int(U32_MAX) + int(1));
{
    return (u64(x) + u64(y)) % (u64(U32_MAX) + u64(1));
}

function u32_wrap_sub(x: u32, y: u32): u32
    ensures int(return) == (int(U32_MAX) + int(1) + int(x) - int(y)) % (int(U32_MAX) + int(1));
{
    return (u64(U32_MAX) + u64(1) + x - y) % (u64(U32_MAX) + u64(1));
}

function u32_wrap_mul(x: u32, y: u32): u32
    ensures int(return) == (int(x) * int(y)) % (int(U32_MAX) + int(1));
{
    return (u64(x) * u64(y)) % (u64(U32_MAX) + u64(1));
}

function u64_wrap_add(x: u64, y: u64): u64
    ensures int(return) == (int(x) + int(y)) % (int(U64_MAX) + int(1));
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
    ensures int(return) == (int(U64_MAX) + int(1) + int(x) - int(y)) % (int(U64_MAX) + int(1));
{
    if x < y {
        return ~(y - x) + 1;
    } else {
        return x - y;
    }
}


// Lemma for multiplying out (xh * M + xl) * (yh * M + yl).
ghost function mul_split_lemma(x: int, y: int,
                               xh: int, xl: int,
                               yh: int, yl: int,
                               M: int)
    requires x == xh * M + xl;
    requires y == yh * M + yl;
    ensures x * y == xh * yh * (M*M) + (xh * yl + xl * yh) * M + xl * yl;
{}


// Modulo calculations.

// (Note: When I was using z3 version 4.12.something, this was all solved automatically.
// But with z3 version 4.13.3, it seems I have to write out all these lemmas manually.
// A bit unfortunate.)

// (TODO: Adding some of these to IntDivision.b might be a good idea.)

// (x*M + y)%M = y%M.
ghost function mod_remove_multiple_of_m(x: int, y: int, M: int)
    requires x >= int(0);
    requires y >= int(0);
    requires M > int(0);
    ensures (x * M + y) % M == y % M;
{
    assert (x*M + y) == (x + y/M)*M + y%M;
}

// (x + y)%M = (x%M + y)%M.
ghost function add_inner_mod(x: int, y: int, M: int)
    requires x >= int(0);
    requires y >= int(0);
    requires M > int(0);
    ensures (x + y) % M == ((x%M) + y) % M;
{
    assert x + y == x/M*M + x%M + y;
    mod_remove_multiple_of_m(x/M, x%M + y, M);
}

// If b%M = c%M, then (a+b)%M = (a+c)%M.
ghost function mod_plus(a: int, b: int, c: int, M: int)
    requires a >= int(0);
    requires b >= int(0);
    requires c >= int(0);
    requires M > int(0);
    requires b % M == c % M;
    ensures (a + b) % M == (a + c) % M;
{
    add_inner_mod(b, a, M);   // (a + b) % M == (a + b%M) % M
    add_inner_mod(c, a, M);   // (a + c) % M == (a + c%M) % M
    // The result now follows from b%M == c%M.
}

// In (a + b*M) % (M*M), you can replace b with b%M.
ghost function mod_mul_m_lemma(a: int, b: int, M: int)
    requires a >= int(0);
    requires b >= int(0);
    requires M > int(0);
    ensures (a + b * M) % (M*M) == (a + (b%M)*M) % (M*M);
{
    assert (b*M) % (M*M) == ((b%M)*M) % (M*M) {
        assert b*M == (b*M) / (M*M) * (M*M) + (b*M) % (M*M);
    }
    mod_plus(a, b*M, b%M*M, M*M);
}

ghost function mul_mod_lemma(a: int, b: int, c: int, d: int, M: int)
    requires a >= int(0);
    requires b >= int(0);
    requires c >= int(0);
    requires d >= int(0);
    requires M > int(0);
    ensures (a * M * M + (b + c) * M + d) % (M*M)
        == ((d + (c%M)*M) % (M*M) + (b%M)*M) % (M*M);
{
    assert (a * M * M + (b + c) * M + d) % (M*M) == ((b + c) * M + d) % (M*M) {
        mod_remove_multiple_of_m(a, (b + c) * M + d, M*M);
    }
    assert ((b + c) * M + d) % (M*M) == ((d + c * M) % (M*M) + b * M) % (M*M) {
        add_inner_mod(d + c * M, b * M, M*M);
    }
    assert ((d+c*M)%(M*M) + b * M) % (M*M) == ((d+c*M)%(M*M) + (b%M) * M) % (M*M) {
        mod_mul_m_lemma((d+c*M)%(M*M), b, M);
    }
    assert (d+c*M)%(M*M) == (d+(c%M)*M)%(M*M) {
        mod_mul_m_lemma(d, c, M);
    }
}

ghost function u64_non_neg(x: u64)
    ensures x >= 0;
{}

function u64_wrap_mul(x: u64, y: u64): u64
    ensures int(return) == (int(x) * int(y)) % (int(U64_MAX) + int(1));
{
    var TWO_TO_32: u64 = u64(U32_MAX) + 1;

    // Split inputs into high and low halves.
    var xh = x / TWO_TO_32;
    var xl = x % TWO_TO_32;
    var yh = y / TWO_TO_32;
    var yl = y % TWO_TO_32;

    ghost mul_split_lemma(int(x), int(y), int(xh), int(xl), int(yh), int(yl), int(TWO_TO_32));
        // proves x*y == (xh*yh)*2^64 + (xh*yl + xl*yh)*2^32 + xl*yl

    // Calculate partial products.
    ghost var hi_hi: u64 = xh * yh;
    var hi_lo: u64 = xh * yl;
    var lo_hi: u64 = xl * yh;
    var lo_lo: u64 = xl * yl;

    // Calculate low 64-bit half of the 128-bit product.
    var z: u64 = u64_wrap_add(lo_lo, (lo_hi % TWO_TO_32) * TWO_TO_32);
    var result: u64 = u64_wrap_add(z, (hi_lo % TWO_TO_32) * TWO_TO_32);

    // Proving the postcondition
    ghost u64_non_neg(hi_lo);
    ghost u64_non_neg(lo_hi);
    ghost u64_non_neg(lo_lo);
    ghost mul_mod_lemma(int(hi_hi), int(hi_lo), int(lo_hi), int(lo_lo), int(TWO_TO_32));

    // Return the low 64-bit half of the product.
    return result;
}
