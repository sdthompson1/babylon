// Basic operations and limits for integers.

module Int

interface {

    //---------------------------------------------------------
    // Integer limits.

    const I8_MIN: i8 = -128;
    const I8_MAX: i8 = 127;
    const U8_MAX: u8 = 255;

    const I16_MIN: i16 = -32768;
    const I16_MAX: i16 = 32767;
    const U16_MAX: u16 = 65535;
    
    const I32_MIN: i32 = -2147483648;
    const I32_MAX: i32 = 2147483647;
    const U32_MAX: u32 = 4294967295;

    const I64_MIN: i64 = -9223372036854775808;
    const I64_MAX: i64 = 9223372036854775807;
    const U64_MAX: u64 = 18446744073709551615;


    //---------------------------------------------------------
    // Min, max, clamp functions.

    // (These are provided for types int, i64 and u64. To use them
    // at smaller types e.g. i8 or u8, you can just use the i64 or
    // u64 versions.)

    ghost function int_min(a: int, b: int): int
    {
        if a <= b {
            return a;
        } else {
            return b;
        }
    }

    function i64_min(a: i64, b: i64): i64
        ensures int(return) == int_min(int(a), int(b));

    function u64_min(a: u64, b: u64): u64
        ensures int(return) == int_min(int(a), int(b));


    ghost function int_max(a: int, b: int): int
    {
        if a >= b {
            return a;
        } else {
            return b;
        }
    }
    
    function i64_max(a: i64, b: i64): i64
        ensures int(return) == int_max(int(a), int(b));

    function u64_max(a: u64, b: u64): u64
        ensures int(return) == int_max(int(a), int(b));


    ghost function int_clamp(x: int, min: int, max: int): int
    {
        if x <= min {
            return min;
        } else if x >= max {
            return max;
        } else {
            return x;
        }
    }

    function i64_clamp(x: i64, min: i64, max: i64): i64
        ensures int(return) == int_clamp(int(x), int(min), int(max));

    function u64_clamp(x: u64, min: u64, max: u64): u64
        ensures int(return) == int_clamp(int(x), int(min), int(max));


    //---------------------------------------------------------
    // Sign and absolute value functions.

    ghost function int_sgn(x: int): int
    {
        if x > int(0) {
            return int(1);
        } else if x < int(0) {
            return int(-1);
        } else {
            return int(0);
        }
    }

    function i64_sgn(x: i64): i64
        ensures int(return) == int_sgn(int(x));

    ghost function int_abs(x: int): int
    {
        if x >= int(0) {
            return x;
        } else {
            return -x;
        }
    }

    function i64_abs(x: i64): i64
        requires x != I64_MIN;
        ensures int(return) == int_abs(int(x));


    //---------------------------------------------------------
    // Determining whether additions, multiplications etc. are
    // possible without overflow.

    ghost function can_add_i8(x: i8, y: i8): bool
    {
        return int(I8_MIN) <= int(x) + int(y) <= int(I8_MAX);
    }

    ghost function can_sub_i8(x: i8, y: i8): bool
    {
        return int(I8_MIN) <= int(x) - int(y) <= int(I8_MAX);
    }

    ghost function can_mul_i8(x: i8, y: i8): bool
    {
        return int(I8_MIN) <= int(x) * int(y) <= int(I8_MAX);
    }

    ghost function can_div_i8(x: i8, y: i8): bool
    {
        return y != 0 && !(x == I8_MIN && y == -1);
    }

    ghost function can_add_i16(x: i16, y: i16): bool
    {
        return int(I16_MIN) <= int(x) + int(y) <= int(I16_MAX);
    }

    ghost function can_sub_i16(x: i16, y: i16): bool
    {
        return int(I16_MIN) <= int(x) - int(y) <= int(I16_MAX);
    }

    ghost function can_mul_i16(x: i16, y: i16): bool
    {
        return int(I16_MIN) <= int(x) * int(y) <= int(I16_MAX);
    }

    ghost function can_div_i16(x: i16, y: i16): bool
    {
        return y != 0 && !(x == I16_MIN && y == -1);
    }

    ghost function can_add_i32(x: i32, y: i32): bool
    {
        return int(I32_MIN) <= int(x) + int(y) <= int(I32_MAX);
    }

    ghost function can_sub_i32(x: i32, y: i32): bool
    {
        return int(I32_MIN) <= int(x) - int(y) <= int(I32_MAX);
    }

    ghost function can_mul_i32(x: i32, y: i32): bool
    {
        return int(I32_MIN) <= int(x) * int(y) <= int(I32_MAX);
    }

    ghost function can_div_i32(x: i32, y: i32): bool
    {
        return y != 0 && !(x == I32_MIN && y == -1);
    }

    ghost function can_add_i64(x: i64, y: i64): bool
    {
        return int(I64_MIN) <= int(x) + int(y) <= int(I64_MAX);
    }

    ghost function can_sub_i64(x: i64, y: i64): bool
    {
        return int(I64_MIN) <= int(x) - int(y) <= int(I64_MAX);
    }

    ghost function can_mul_i64(x: i64, y: i64): bool
    {
        return int(I64_MIN) <= int(x) * int(y) <= int(I64_MAX);
    }

    ghost function can_div_i64(x: i64, y: i64): bool
    {
        return y != 0 && !(x == I64_MIN && y == -1);
    }

    ghost function can_add_u8(x: u8, y: u8): bool
    {
        return int(x) + int(y) <= int(U8_MAX);
    }

    ghost function can_sub_u8(x: u8, y: u8): bool
    {
        return int(0) <= int(x) - int(y) <= int(U8_MAX);
    }

    ghost function can_mul_u8(x: u8, y: u8): bool
    {
        return int(x) * int(y) <= int(U8_MAX);
    }

    ghost function can_div_u8(x: u8, y: u8): bool
    {
        return y != 0;
    }

    ghost function can_add_u16(x: u16, y: u16): bool
    {
        return int(x) + int(y) <= int(U16_MAX);
    }

    ghost function can_sub_u16(x: u16, y: u16): bool
    {
        return int(0) <= int(x) - int(y) <= int(U16_MAX);
    }

    ghost function can_mul_u16(x: u16, y: u16): bool
    {
        return int(x) * int(y) <= int(U16_MAX);
    }

    ghost function can_div_u16(x: u16, y: u16): bool
    {
        return y != 0;
    }

    ghost function can_add_u32(x: u32, y: u32): bool
    {
        return int(x) + int(y) <= int(U32_MAX);
    }

    ghost function can_sub_u32(x: u32, y: u32): bool
    {
        return int(0) <= int(x) - int(y) <= int(U32_MAX);
    }

    ghost function can_mul_u32(x: u32, y: u32): bool
    {
        return int(x) * int(y) <= int(U32_MAX);
    }

    ghost function can_div_u32(x: u32, y: u32): bool
    {
        return y != 0;
    }

    ghost function can_add_u64(x: u64, y: u64): bool
    {
        return int(x) + int(y) <= int(U64_MAX);
    }

    ghost function can_sub_u64(x: u64, y: u64): bool
    {
        return int(0) <= int(x) - int(y) <= int(U64_MAX);
    }

    ghost function can_mul_u64(x: u64, y: u64): bool
    {
        return int(x) * int(y) <= int(U64_MAX);
    }

    ghost function can_div_u64(x: u64, y: u64): bool
    {
        return y != 0;
    }
}

function i64_min(a: i64, b: i64): i64
    ensures int(return) == int_min(int(a), int(b));
{
    if a <= b {
        return a;
    } else {
        return b;
    }
}

function u64_min(a: u64, b: u64): u64
    ensures int(return) == int_min(int(a), int(b));
{
    if a <= b {
        return a;
    } else {
        return b;
    }
}

function i64_max(a: i64, b: i64): i64
    ensures int(return) == int_max(int(a), int(b));
{
    if a >= b {
        return a;
    } else {
        return b;
    }
}

function u64_max(a: u64, b: u64): u64
    ensures int(return) == int_max(int(a), int(b));
{
    if a >= b {
        return a;
    } else {
        return b;
    }
}

function i64_clamp(x: i64, min: i64, max: i64): i64
    ensures int(return) == int_clamp(int(x), int(min), int(max));
{
    if x <= min {
        return min;
    } else if x >= max {
        return max;
    } else {
        return x;
    }
}

function u64_clamp(x: u64, min: u64, max: u64): u64
    ensures int(return) == int_clamp(int(x), int(min), int(max));
{
    if x <= min {
        return min;
    } else if x >= max {
        return max;
    } else {
        return x;
    }
}

function i64_sgn(x: i64): i64
    ensures int(return) == int_sgn(int(x));
{
    if x > 0 {
        return 1;
    } else if x < 0 {
        return -1;
    } else {
        return 0;
    }
}

function i64_abs(x: i64): i64
    requires x != I64_MIN;
    ensures int(return) == int_abs(int(x));
{
    if x >= 0 {
        return x;
    } else {
        return -x;
    }
}
