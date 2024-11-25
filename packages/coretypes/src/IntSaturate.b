// Saturating integer arithmetic.
// Operations that overflow will be clamped to the relevant MIN or MAX value.

module IntSaturate

import Int;

interface {
    // i8 operations

    function i8_sat_add(x: i8, y: i8): i8
        ensures int(return) == int_clamp(int(x) + int(y), int(I8_MIN), int(I8_MAX));

    function i8_sat_sub(x: i8, y: i8): i8
        ensures int(return) == int_clamp(int(x) - int(y), int(I8_MIN), int(I8_MAX));

    function i8_sat_mul(x: i8, y: i8): i8
        ensures int(return) == int_clamp(int(x) * int(y), int(I8_MIN), int(I8_MAX));

    function i8_sat_div(x: i8, y: i8): i8
        requires y != 0;
        ensures int(return) == int_clamp(int(x) / int(y), int(I8_MIN), int(I8_MAX));


    // i16 operations

    function i16_sat_add(x: i16, y: i16): i16
        ensures int(return) == int_clamp(int(x) + int(y), int(I16_MIN), int(I16_MAX));

    function i16_sat_sub(x: i16, y: i16): i16
        ensures int(return) == int_clamp(int(x) - int(y), int(I16_MIN), int(I16_MAX));

    function i16_sat_mul(x: i16, y: i16): i16
        ensures int(return) == int_clamp(int(x) * int(y), int(I16_MIN), int(I16_MAX));

    function i16_sat_div(x: i16, y: i16): i16
        requires y != 0;
        ensures int(return) == int_clamp(int(x) / int(y), int(I16_MIN), int(I16_MAX));


    // i32 operations

    function i32_sat_add(x: i32, y: i32): i32
        ensures int(return) == int_clamp(int(x) + int(y), int(I32_MIN), int(I32_MAX));

    function i32_sat_sub(x: i32, y: i32): i32
        ensures int(return) == int_clamp(int(x) - int(y), int(I32_MIN), int(I32_MAX));

    function i32_sat_mul(x: i32, y: i32): i32
        ensures int(return) == int_clamp(int(x) * int(y), int(I32_MIN), int(I32_MAX));

    function i32_sat_div(x: i32, y: i32): i32
        requires y != 0;
        ensures int(return) == int_clamp(int(x) / int(y), int(I32_MIN), int(I32_MAX));


    // i64 operations

    function i64_sat_add(x: i64, y: i64): i64
        ensures int(return) == int_clamp(int(x) + int(y), int(I64_MIN), int(I64_MAX));

    function i64_sat_sub(x: i64, y: i64): i64
        ensures int(return) == int_clamp(int(x) - int(y), int(I64_MIN), int(I64_MAX));

    function i64_sat_mul(x: i64, y: i64): i64
        ensures int(return) == int_clamp(int(x) * int(y), int(I64_MIN), int(I64_MAX));

    function i64_sat_div(x: i64, y: i64): i64
        requires y != 0;
        ensures int(return) == int_clamp(int(x) / int(y), int(I64_MIN), int(I64_MAX));


    // u8 operations

    function u8_sat_add(x: u8, y: u8): u8
        ensures int(return) == int_clamp(int(x) + int(y), int(0), int(U8_MAX));

    function u8_sat_sub(x: u8, y: u8): u8
        ensures int(return) == int_clamp(int(x) - int(y), int(0), int(U8_MAX));

    function u8_sat_mul(x: u8, y: u8): u8
        ensures int(return) == int_clamp(int(x) * int(y), int(0), int(U8_MAX));


    // u16 operations

    function u16_sat_add(x: u16, y: u16): u16
        ensures int(return) == int_clamp(int(x) + int(y), int(0), int(U16_MAX));

    function u16_sat_sub(x: u16, y: u16): u16
        ensures int(return) == int_clamp(int(x) - int(y), int(0), int(U16_MAX));

    function u16_sat_mul(x: u16, y: u16): u16
        ensures int(return) == int_clamp(int(x) * int(y), int(0), int(U16_MAX));


    // u32 operations

    function u32_sat_add(x: u32, y: u32): u32
        ensures int(return) == int_clamp(int(x) + int(y), int(0), int(U32_MAX));

    function u32_sat_sub(x: u32, y: u32): u32
        ensures int(return) == int_clamp(int(x) - int(y), int(0), int(U32_MAX));

    function u32_sat_mul(x: u32, y: u32): u32
        ensures int(return) == int_clamp(int(x) * int(y), int(0), int(U32_MAX));


    // u64 operations

    function u64_sat_add(x: u64, y: u64): u64
        ensures int(return) == int_clamp(int(x) + int(y), int(0), int(U64_MAX));

    function u64_sat_sub(x: u64, y: u64): u64
        ensures int(return) == int_clamp(int(x) - int(y), int(0), int(U64_MAX));

    function u64_sat_mul(x: u64, y: u64): u64
        ensures int(return) == int_clamp(int(x) * int(y), int(0), int(U64_MAX));

}

function i8_sat_add(x: i8, y: i8): i8
    ensures int(return) == int_clamp(int(x) + int(y), int(I8_MIN), int(I8_MAX));
{
    return i64_clamp(i64(x) + i64(y), I8_MIN, I8_MAX);
}

function i8_sat_sub(x: i8, y: i8): i8
    ensures int(return) == int_clamp(int(x) - int(y), int(I8_MIN), int(I8_MAX));
{
    return i64_clamp(i64(x) - i64(y), I8_MIN, I8_MAX);
}

function i8_sat_mul(x: i8, y: i8): i8
    ensures int(return) == int_clamp(int(x) * int(y), int(I8_MIN), int(I8_MAX));
{
    return i64_clamp(i64(x) * i64(y), I8_MIN, I8_MAX);
}

function i8_sat_div(x: i8, y: i8): i8
    requires y != 0;
    ensures int(return) == int_clamp(int(x) / int(y), int(I8_MIN), int(I8_MAX));
{
    return i64_clamp(i64(x) / i64(y), I8_MIN, I8_MAX);
}

function i16_sat_add(x: i16, y: i16): i16
    ensures int(return) == int_clamp(int(x) + int(y), int(I16_MIN), int(I16_MAX));
{
    return i64_clamp(i64(x) + i64(y), I16_MIN, I16_MAX);
}

function i16_sat_sub(x: i16, y: i16): i16
    ensures int(return) == int_clamp(int(x) - int(y), int(I16_MIN), int(I16_MAX));
{
    return i64_clamp(i64(x) - i64(y), I16_MIN, I16_MAX);
}

function i16_sat_mul(x: i16, y: i16): i16
    ensures int(return) == int_clamp(int(x) * int(y), int(I16_MIN), int(I16_MAX));
{
    return i64_clamp(i64(x) * i64(y), I16_MIN, I16_MAX);
}

function i16_sat_div(x: i16, y: i16): i16
    requires y != 0;
    ensures int(return) == int_clamp(int(x) / int(y), int(I16_MIN), int(I16_MAX));
{
    return i64_clamp(i64(x) / i64(y), I16_MIN, I16_MAX);
}

function i32_sat_add(x: i32, y: i32): i32
    ensures int(return) == int_clamp(int(x) + int(y), int(I32_MIN), int(I32_MAX));
{
    return i64_clamp(i64(x) + i64(y), I32_MIN, I32_MAX);
}

function i32_sat_sub(x: i32, y: i32): i32
    ensures int(return) == int_clamp(int(x) - int(y), int(I32_MIN), int(I32_MAX));
{
    return i64_clamp(i64(x) - i64(y), I32_MIN, I32_MAX);
}

function i32_sat_mul(x: i32, y: i32): i32
    ensures int(return) == int_clamp(int(x) * int(y), int(I32_MIN), int(I32_MAX));
{
    return i64_clamp(i64(x) * i64(y), I32_MIN, I32_MAX);
}

function i32_sat_div(x: i32, y: i32): i32
    requires y != 0;
    ensures int(return) == int_clamp(int(x) / int(y), int(I32_MIN), int(I32_MAX));
{
    return i64_clamp(i64(x) / i64(y), I32_MIN, I32_MAX);
}

function i64_sat_add(x: i64, y: i64): i64
    ensures int(return) == int_clamp(int(x) + int(y), int(I64_MIN), int(I64_MAX));
{
    if x >= 0 {
        if y > I64_MAX - x {
            return I64_MAX;
        } else {
            return x + y;
        }
    } else {
        if y < I64_MIN - x {
            return I64_MIN;
        } else {
            return x + y;
        }
    }
}

function i64_sat_sub(x: i64, y: i64): i64
    ensures int(return) == int_clamp(int(x) - int(y), int(I64_MIN), int(I64_MAX));
{
    if x >= -1 {
        if y < -I64_MAX + x {
            return I64_MAX;
        } else {
            return x - y;
        }
    } else {
        if y > I64_MAX + x + 1 {
            return I64_MIN;
        } else {
            return x - y;
        }
    }
}

// Helper function
function will_multiply_overflow(x: i64, y: i64): bool
    ensures return <==> !(int(I64_MIN) <= int(x)*int(y) <= int(I64_MAX));
{
    if x == 0 || y == 0 { return false; }
    if x == -1 { return y == I64_MIN; }
    if y == -1 { return x == I64_MIN; }

    if x > 0 && y > 0 { return x > I64_MAX / y; }
    if x < 0 && y < 0 { return x < I64_MAX / y; }
    if x > 0 && y < 0 { return y < I64_MIN / x; }
    if x < 0 && y > 0 { return x < I64_MIN / y; }

    return false;
}

function i64_sat_mul(x: i64, y: i64): i64
    ensures int(return) == int_clamp(int(x) * int(y), int(I64_MIN), int(I64_MAX));
{
    if will_multiply_overflow(x, y) {
        if x > 0 && y > 0 || x < 0 && y < 0 {
            return I64_MAX;
        } else {
            return I64_MIN;
        }
    } else {
        return x * y;
    }
}

function i64_sat_div(x: i64, y: i64): i64
    requires y != 0;
    ensures int(return) == int_clamp(int(x) / int(y), int(I64_MIN), int(I64_MAX));
{
    if x == I64_MIN && y == -1 {
        return I64_MAX;
    } else {
        return x / y;
    }
}


function u8_sat_add(x: u8, y: u8): u8
    ensures int(return) == int_clamp(int(x) + int(y), int(0), int(U8_MAX));
{
    return u64_min(u64(x) + u64(y), U8_MAX);
}

function u8_sat_sub(x: u8, y: u8): u8
    ensures int(return) == int_clamp(int(x) - int(y), int(0), int(U8_MAX));
{
    return i64_clamp(i64(x) - i64(y), 0, U8_MAX);
}

function u8_sat_mul(x: u8, y: u8): u8
    ensures int(return) == int_clamp(int(x) * int(y), int(0), int(U8_MAX));
{
    return u64_min(u64(x) * u64(y), U8_MAX);
}

function u16_sat_add(x: u16, y: u16): u16
    ensures int(return) == int_clamp(int(x) + int(y), int(0), int(U16_MAX));
{
    return u64_min(u64(x) + u64(y), U16_MAX);
}

function u16_sat_sub(x: u16, y: u16): u16
    ensures int(return) == int_clamp(int(x) - int(y), int(0), int(U16_MAX));
{
    return i64_clamp(i64(x) - i64(y), 0, U16_MAX);
}

function u16_sat_mul(x: u16, y: u16): u16
    ensures int(return) == int_clamp(int(x) * int(y), int(0), int(U16_MAX));
{
    return u64_min(u64(x) * u64(y), U16_MAX);
}

function u32_sat_add(x: u32, y: u32): u32
    ensures int(return) == int_clamp(int(x) + int(y), int(0), int(U32_MAX));
{
    return u64_min(u64(x) + u64(y), U32_MAX);
}

function u32_sat_sub(x: u32, y: u32): u32
    ensures int(return) == int_clamp(int(x) - int(y), int(0), int(U32_MAX));
{
    return i64_clamp(i64(x) - i64(y), 0, U32_MAX);
}

function u32_sat_mul(x: u32, y: u32): u32
    ensures int(return) == int_clamp(int(x) * int(y), int(0), int(U32_MAX));
{
    return u64_min(u64(x) * u64(y), U32_MAX);
}

function u64_sat_add(x: u64, y: u64): u64
    ensures int(return) == int_clamp(int(x) + int(y), int(0), int(U64_MAX));
{
    if y > U64_MAX - x {
        return U64_MAX;
    } else {
        return x + y;
    }
}

function u64_sat_sub(x: u64, y: u64): u64
    ensures int(return) == int_clamp(int(x) - int(y), int(0), int(U64_MAX));
{
    if y > x {
        return 0;
    } else {
        return x - y;
    }
}

function u64_sat_mul(x: u64, y: u64): u64
    ensures int(return) == int_clamp(int(x) * int(y), int(0), int(U64_MAX));
{
    if y == 0 {
        return 0;
    } else if x > U64_MAX / y {
        return U64_MAX;
    } else {
        return x * y;
    }
}
