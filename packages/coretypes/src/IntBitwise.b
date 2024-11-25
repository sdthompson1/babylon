module IntBitwise

// Bitwise rotation operators, for unsigned integer types.

// (Note that other bitwise operators -- shifts, AND, OR etc. -- are
// already available as operators in the language. However, rotation
// is not currently built-in, instead it is implemented here.)

interface {
    function u8_rol(x: u8, y: u8): u8
        requires 0 <= y <= 8;

    function u8_ror(x: u8, y: u8): u8
        requires 0 <= y <= 8;

    function u16_rol(x: u16, y: u16): u16
        requires 0 <= y <= 16;

    function u16_ror(x: u16, y: u16): u16
        requires 0 <= y <= 16;

    function u32_rol(x: u32, y: u32): u32
        requires 0 <= y <= 32;

    function u32_ror(x: u32, y: u32): u32
        requires 0 <= y <= 32;

    function u64_rol(x: u64, y: u64): u64
        requires 0 <= y <= 64;

    function u64_ror(x: u64, y: u64): u64
        requires 0 <= y <= 64;
}

import Int;

function u8_rol(x: u8, y: u8): u8
    requires 0 <= y <= 8;
{
    if y == 0 || y == 8 {
        return x;
    } else {
        return ((x & (U8_MAX >> y)) << y) | (x >> (8 - y));
    }
}

function u8_ror(x: u8, y: u8): u8
    requires 0 <= y <= 8;
{
    return u8_rol(x, 8 - y);
}

function u16_rol(x: u16, y: u16): u16
    requires 0 <= y <= 16;
{
    if y == 0 || y == 16 {
        return x;
    } else {
        return ((x & (U16_MAX >> y)) << y) | (x >> (16 - y));
    }
}

function u16_ror(x: u16, y: u16): u16
    requires 0 <= y <= 16;
{
    return u16_rol(x, 16 - y);
}

function u32_rol(x: u32, y: u32): u32
    requires 0 <= y <= 32;
{
    if y == 0 || y == 32 {
        return x;
    } else {
        return ((x & (U32_MAX >> y)) << y) | (x >> (32 - y));
    }
}

function u32_ror(x: u32, y: u32): u32
    requires 0 <= y <= 32;
{
    return u32_rol(x, 32 - y);
}

function u64_rol(x: u64, y: u64): u64
    requires 0 <= y <= 64;
{
    if y == 0 || y == 64 {
        return x;
    } else {
        // note: this is slow to verify (approx 30 sec, using cvc5, on my machine)
        return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
    }
}

function u64_ror(x: u64, y: u64): u64
    requires 0 <= y <= 64;
{
    return u64_rol(x, 64 - y);
}

// Some quick test cases

ghost function rotate_tests()
{
    assert u8_ror(15, 1) == 135;
    assert u8_rol(123, 2) == 237;
    assert u8_ror(123, 2) == 222;
    assert u16_rol(12345, 2) == 49380;
    assert u16_ror(12345, 2) == 19470;
    assert u32_rol(987654321, 10) == 2040710379;
    assert u32_ror(987654321, 10) == 743356314;
    assert u64_rol(1, 1) == 2;
    assert u64_rol(1, 3) == 8;
    assert u64_rol(15, 62) == (u64(I64_MAX) + 1) + ((u64(I64_MAX) + 1) >> 1) + 3;
    assert u64_rol(1311768467463790320, 27) == 14183496552161583795;
    assert u64_ror(1311768467463790320, 27) == 6312883404044685075;
}
