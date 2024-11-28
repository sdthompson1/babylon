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
        // Unfortunately, verifying the following statement is very slow:
        // return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));

        // To work around this, we split into cases based on y
        // (this is not optimal, but it is good enough for now -- eventually, building
        // a rotate operator into the compiler might be a better solution).

        match y {
        case 1 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 2 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 3 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 4 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 5 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 6 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 7 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 8 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 9 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 10 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 11 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 12 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 13 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 14 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 15 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 16 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 17 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 18 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 19 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 20 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 21 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 22 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 23 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 24 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 25 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 26 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 27 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 28 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 29 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 30 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 31 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 32 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 33 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 34 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 35 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 36 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 37 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 38 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 39 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 40 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 41 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 42 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 43 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 44 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 45 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 46 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 47 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 48 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 49 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 50 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 51 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 52 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 53 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 54 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 55 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 56 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 57 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 58 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 59 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 60 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 61 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 62 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        case 63 => return ((x & (U64_MAX >> y)) << y) | (x >> (64 - y));
        }
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
