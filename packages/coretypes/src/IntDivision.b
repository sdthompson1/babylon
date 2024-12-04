// Alternative forms of integer division.

module IntDivision

import Int;

interface {
    //---------------------------------------------------------
    // Euclidean division.

    // This always yields a non-negative remainder.

    ghost function int_euclid_div(x: int, y: int): {quot: int, rem: int}
        requires y != int(0);
        ensures x == return.quot * y + return.rem;
        ensures int(0) <= return.rem < int_abs(y);

    // Lemma: The result of Euclidean division is unique; i.e. if {q,r}
    // is any pair of integers such that x = q*y + r, and r is in the
    // correct range, then {q,r} is equal to int_euclid_div(x,y).
    
    ghost function int_euclid_div_unique(x: int, y: int, q: int, r: int)
        requires y != int(0);
        requires x == q * y + r;
        requires int(0) <= r < int_abs(y);
        ensures {quot = q, rem = r} == int_euclid_div(x, y);

    // Implementations of Euclidean division for the built-in signed
    // integer types. (Note that for unsigned integers, Euclidean
    // division is equivalent to the usual "/" and "%" operators, so
    // no "unsigned" versions are provided.)

    function i8_euclid_div(x: i8, y: i8): {quot: i8, rem: i8}
        requires y != 0;
        requires !(x == I8_MIN && y == -1);
        ensures int(return.quot) == int_euclid_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_euclid_div(int(x), int(y)).rem;

    function i16_euclid_div(x: i16, y: i16): {quot: i16, rem: i16}
        requires y != 0;
        requires !(x == I16_MIN && y == -1);
        ensures int(return.quot) == int_euclid_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_euclid_div(int(x), int(y)).rem;

    function i32_euclid_div(x: i32, y: i32): {quot: i32, rem: i32}
        requires y != 0;
        requires !(x == I32_MIN && y == -1);
        ensures int(return.quot) == int_euclid_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_euclid_div(int(x), int(y)).rem;

    function i64_euclid_div(x: i64, y: i64): {quot: i64, rem: i64}
        requires y != 0;
        requires !(x == I64_MIN && y == -1);
        ensures int(return.quot) == int_euclid_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_euclid_div(int(x), int(y)).rem;


    //---------------------------------------------------------
    // Floor division.

    // This always rounds the quotient downwards (towards minus infinity).

    // Note that this is the same as Euclidean division for positive
    // divisors, but differs for negative divisors.

    ghost function int_floor_div(x: int, y: int): {quot: int, rem: int}
        requires y != int(0);
        ensures x == return.quot * y + return.rem;
        ensures -int_abs(y) < return.rem < int_abs(y);
        ensures y > int(0) ==> return.quot * y <= x;   // i.e. quot <= x/y
        ensures y < int(0) ==> return.quot * y >= x;   // i.e. quot <= x/y

    ghost function int_floor_div_unique(x: int, y: int, q: int, r: int)
        requires y != int(0);
        requires x == q * y + r;
        requires -int_abs(y) < r < int_abs(y);
        requires y > int(0) ==> q * y <= x;
        requires y < int(0) ==> q * y >= x;
        ensures {quot = q, rem = r} == int_floor_div(x, y);

    function i8_floor_div(x: i8, y: i8): {quot: i8, rem: i8}
        requires y != 0;
        requires !(x == I8_MIN && y == -1);
        ensures int(return.quot) == int_floor_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_floor_div(int(x), int(y)).rem;

    function i16_floor_div(x: i16, y: i16): {quot: i16, rem: i16}
        requires y != 0;
        requires !(x == I16_MIN && y == -1);
        ensures int(return.quot) == int_floor_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_floor_div(int(x), int(y)).rem;

    function i32_floor_div(x: i32, y: i32): {quot: i32, rem: i32}
        requires y != 0;
        requires !(x == I32_MIN && y == -1);
        ensures int(return.quot) == int_floor_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_floor_div(int(x), int(y)).rem;

    function i64_floor_div(x: i64, y: i64): {quot: i64, rem: i64}
        requires y != 0;
        requires !(x == I64_MIN && y == -1);
        ensures int(return.quot) == int_floor_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_floor_div(int(x), int(y)).rem;


    //---------------------------------------------------------
    // Ceiling division.

    // This is the opposite of floor division -- the quotient is
    // rounded towards plus infinity.

    ghost function int_ceil_div(x: int, y: int): {quot: int, rem: int}
        requires y != int(0);
        ensures x == return.quot * y + return.rem;
        ensures -int_abs(y) < return.rem < int_abs(y);
        ensures y > int(0) ==> return.quot * y >= x;   // i.e. quot >= x/y
        ensures y < int(0) ==> return.quot * y <= x;   // i.e. quot >= x/y

    ghost function int_ceil_div_unique(x: int, y: int, q: int, r: int)
        requires y != int(0);
        requires x == q * y + r;
        requires -int_abs(y) < r < int_abs(y);
        requires y > int(0) ==> q * y >= x;
        requires y < int(0) ==> q * y <= x;
        ensures {quot = q, rem = r} == int_ceil_div(x, y);

    function i8_ceil_div(x: i8, y: i8): {quot: i8, rem: i8}
        requires y != 0;
        requires !(x == I8_MIN && y == -1);
        ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_ceil_div(int(x), int(y)).rem;

    function i16_ceil_div(x: i16, y: i16): {quot: i16, rem: i16}
        requires y != 0;
        requires !(x == I16_MIN && y == -1);
        ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_ceil_div(int(x), int(y)).rem;

    function i32_ceil_div(x: i32, y: i32): {quot: i32, rem: i32}
        requires y != 0;
        requires !(x == I32_MIN && y == -1);
        ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_ceil_div(int(x), int(y)).rem;

    function i64_ceil_div(x: i64, y: i64): {quot: i64, rem: i64}
        requires y != 0;
        requires !(x == I64_MIN && y == -1);
        ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
        ensures int(return.rem) == int_ceil_div(int(x), int(y)).rem;

    // Unsigned ceiling division. In this case the remainder is always
    // negative or zero, so we return the absolute value of the remainder.

    function u8_ceil_div(x: u8, y: u8): {quot: u8, abs_rem: u8}
        requires y != 0;
        ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
        ensures - int(return.abs_rem) == int_ceil_div(int(x), int(y)).rem;

    function u16_ceil_div(x: u16, y: u16): {quot: u16, abs_rem: u16}
        requires y != 0;
        ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
        ensures - int(return.abs_rem) == int_ceil_div(int(x), int(y)).rem;

    function u32_ceil_div(x: u32, y: u32): {quot: u32, abs_rem: u32}
        requires y != 0;
        ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
        ensures - int(return.abs_rem) == int_ceil_div(int(x), int(y)).rem;

    function u64_ceil_div(x: u64, y: u64): {quot: u64, abs_rem: u64}
        requires y != 0;
        ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
        ensures - int(return.abs_rem) == int_ceil_div(int(x), int(y)).rem;

}


// We can define int_euclid_div in terms of the / and % operators.

ghost function int_euclid_div(x: int, y: int): {quot: int, rem: int}
    requires y != int(0);
    ensures x == return.quot * y + return.rem;
    ensures int(0) <= return.rem < int_abs(y);
{
    var q = x / y;
    var r = x % y;
    if r >= int(0) {
        return {quot = q, rem = r};
    } else if y > int(0) {
        return {quot = q - int(1), rem = r + int(y)};
    } else {
        return {quot = q + int(1), rem = r - int(y)};
    }
}

// Proof of int_euclid_div_unique.

ghost function division_uniqueness(x: int, y: int, q1: int, r1: int, q2: int, r2: int)
    requires y != int(0);
    requires x == q1 * y + r1;
    requires int(0) <= r1 < int_abs(y);
    requires x == q2 * y + r2;
    requires int(0) <= r2 < int_abs(y);
    ensures q1 == q2;
    ensures r1 == r2;
{
    assert q1 == q2;
    assert r1 == x - q1 * y;
    assert r2 == x - q2 * y;
    assert r1 == r2;
}

ghost function int_euclid_div_unique(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires x == q * y + r;
    requires int(0) <= r < int_abs(y);
    ensures {quot = q, rem = r} == int_euclid_div(x, y);
{
    var div = int_euclid_div(x, y);
    division_uniqueness(x, y, div.quot, div.rem, q, r);
}

// Implementing Euclidean division for all four of the signed integer types.

function i8_euclid_div(x: i8, y: i8): {quot: i8, rem: i8}
    requires y != 0;
    requires !(x == I8_MIN && y == -1);
    ensures int(return.quot) == int_euclid_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_euclid_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r >= 0 {
        return {quot = q, rem = r};
    } else if y > 0 {
        return {quot = q - i8(1), rem = r + y};
    } else {
        return {quot = q + i8(1), rem = r - y};
    }
}

function i16_euclid_div(x: i16, y: i16): {quot: i16, rem: i16}
    requires y != 0;
    requires !(x == I16_MIN && y == -1);
    ensures int(return.quot) == int_euclid_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_euclid_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r >= 0 {
        return {quot = q, rem = r};
    } else if y > 0 {
        return {quot = q - i16(1), rem = r + y};
    } else {
        return {quot = q + i16(1), rem = r - y};
    }
}

function i32_euclid_div(x: i32, y: i32): {quot: i32, rem: i32}
    requires y != 0;
    requires !(x == I32_MIN && y == -1);
    ensures int(return.quot) == int_euclid_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_euclid_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r >= 0 {
        return {quot = q, rem = r};
    } else if y > 0 {
        return {quot = q - 1, rem = r + y};
    } else {
        return {quot = q + 1, rem = r - y};
    }
}

function i64_euclid_div(x: i64, y: i64): {quot: i64, rem: i64}
    requires y != 0;
    requires !(x == I64_MIN && y == -1);
    ensures int(return.quot) == int_euclid_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_euclid_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r >= 0 {
        return {quot = q, rem = r};
    } else if y > 0 {
        return {quot = q - 1, rem = r + y};
    } else {
        return {quot = q + 1, rem = r - y};
    }
}


// Floor division.

ghost function int_floor_div(x: int, y: int): {quot: int, rem: int}
    requires y != int(0);
    ensures x == return.quot * y + return.rem;
    ensures -int_abs(y) < return.rem < int_abs(y);
    ensures y > int(0) ==> return.quot * y <= x;
    ensures y < int(0) ==> return.quot * y >= x;
{
    var q = x / y;
    var r = x % y;
    if r < int(0) && y > int(0) || r > int(0) && y < int(0) {
        return {quot = q - int(1), rem = r + y};
    } else {
        return {quot = q, rem = r};
    }
}

ghost function int_floor_div_unique(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires x == q * y + r;
    requires -int_abs(y) < r < int_abs(y);
    requires y > int(0) ==> q * y <= x;
    requires y < int(0) ==> q * y >= x;
    ensures {quot = q, rem = r} == int_floor_div(x, y);
{
    // This is most easily proved by exploiting the relationship between
    // floor and Euclidean division.
    if y >= int(0) || r == int(0) {
        int_euclid_div_unique(x, y, q, r);
        return;
    } else {
        int_euclid_div_unique(x, y, q + int(1), r - y);
        return;
    }
}

function i8_floor_div(x: i8, y: i8): {quot: i8, rem: i8}
    requires y != 0;
    requires !(x == I8_MIN && y == -1);
    ensures int(return.quot) == int_floor_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_floor_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r < 0 && y > 0 || r > 0 && y < 0 {
        return {quot = q - i8(1), rem = r + y};
    } else {
        return {quot = q, rem = r};
    }
}

function i16_floor_div(x: i16, y: i16): {quot: i16, rem: i16}
    requires y != 0;
    requires !(x == I16_MIN && y == -1);
    ensures int(return.quot) == int_floor_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_floor_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r < 0 && y > 0 || r > 0 && y < 0 {
        return {quot = q - i8(1), rem = r + y};
    } else {
        return {quot = q, rem = r};
    }
}

function i32_floor_div(x: i32, y: i32): {quot: i32, rem: i32}
    requires y != 0;
    requires !(x == I32_MIN && y == -1);
    ensures int(return.quot) == int_floor_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_floor_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r < 0 && y > 0 || r > 0 && y < 0 {
        return {quot = q - i8(1), rem = r + y};
    } else {
        return {quot = q, rem = r};
    }
}

function i64_floor_div(x: i64, y: i64): {quot: i64, rem: i64}
    requires y != 0;
    requires !(x == I64_MIN && y == -1);
    ensures int(return.quot) == int_floor_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_floor_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r < 0 && y > 0 || r > 0 && y < 0 {
        return {quot = q - i8(1), rem = r + y};
    } else {
        return {quot = q, rem = r};
    }
}


// Ceiling division.

ghost function int_ceil_div(x: int, y: int): {quot: int, rem: int}
    requires y != int(0);
    ensures x == return.quot * y + return.rem;
    ensures -int_abs(y) < return.rem < int_abs(y);
    ensures y > int(0) ==> return.quot * y >= x;   // i.e. quot >= x/y
    ensures y < int(0) ==> return.quot * y <= x;   // i.e. quot >= x/y
{
    var q = x / y;
    var r = x % y;
    if r < int(0) && y < int(0) || r > int(0) && y > int(0) {
        return {quot = q + int(1), rem = r - y};
    } else {
        return {quot = q, rem = r};
    }
}

ghost function int_ceil_div_unique(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires x == q * y + r;
    requires -int_abs(y) < r < int_abs(y);
    requires y > int(0) ==> q * y >= x;
    requires y < int(0) ==> q * y <= x;
    ensures {quot = q, rem = r} == int_ceil_div(x, y);
{
    if y <= int(0) || r == int(0) {
        int_euclid_div_unique(x, y, q, r);
    } else {
        int_euclid_div_unique(x, y, q - int(1), r + y);
    }
}

function i8_ceil_div(x: i8, y: i8): {quot: i8, rem: i8}
    requires y != 0;
    requires !(x == I8_MIN && y == -1);
    ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_ceil_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r < 0 && y < 0 || r > 0 && y > 0 {
        return {quot = q + i8(1), rem = r - y};
    } else {
        return {quot = q, rem = r};
    }
}

function i16_ceil_div(x: i16, y: i16): {quot: i16, rem: i16}
    requires y != 0;
    requires !(x == I16_MIN && y == -1);
    ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_ceil_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r < 0 && y < 0 || r > 0 && y > 0 {
        return {quot = q + i16(1), rem = r - y};
    } else {
        return {quot = q, rem = r};
    }
}

function i32_ceil_div(x: i32, y: i32): {quot: i32, rem: i32}
    requires y != 0;
    requires !(x == I32_MIN && y == -1);
    ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_ceil_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r < 0 && y < 0 || r > 0 && y > 0 {
        return {quot = q + i32(1), rem = r - y};
    } else {
        return {quot = q, rem = r};
    }
}

function i64_ceil_div(x: i64, y: i64): {quot: i64, rem: i64}
    requires y != 0;
    requires !(x == I64_MIN && y == -1);
    ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
    ensures int(return.rem) == int_ceil_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r < 0 && y < 0 || r > 0 && y > 0 {
        return {quot = q + i64(1), rem = r - y};
    } else {
        return {quot = q, rem = r};
    }
}

function u8_ceil_div(x: u8, y: u8): {quot: u8, abs_rem: u8}
    requires y != 0;
    ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
    ensures - int(return.abs_rem) == int_ceil_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r > 0 {
        return {quot = q + u8(1), abs_rem = y - r};
    } else {
        return {quot = q, abs_rem = u8(0)};
    }
}

function u16_ceil_div(x: u16, y: u16): {quot: u16, abs_rem: u16}
    requires y != 0;
    ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
    ensures - int(return.abs_rem) == int_ceil_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r > 0 {
        return {quot = q + u16(1), abs_rem = y - r};
    } else {
        return {quot = q, abs_rem = u16(0)};
    }
}

function u32_ceil_div(x: u32, y: u32): {quot: u32, abs_rem: u32}
    requires y != 0;
    ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
    ensures - int(return.abs_rem) == int_ceil_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r > 0 {
        return {quot = q + u32(1), abs_rem = y - r};
    } else {
        return {quot = q, abs_rem = u32(0)};
    }
}

function u64_ceil_div(x: u64, y: u64): {quot: u64, abs_rem: u64}
    requires y != 0;
    ensures int(return.quot) == int_ceil_div(int(x), int(y)).quot;
    ensures - int(return.abs_rem) == int_ceil_div(int(x), int(y)).rem;
{
    var q = x / y;
    var r = x % y;
    if r > 0 {
        return {quot = q + u64(1), abs_rem = y - r};
    } else {
        return {quot = q, abs_rem = u64(0)};
    }
}
