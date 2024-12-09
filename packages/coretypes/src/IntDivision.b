// Alternative forms of integer division.

module IntDivision

import Int;

interface {

    //---------------------------------------------------------
    // "Modulo" function.

    // This function "reduces" an integer to the range [0, n)
    // by adding or subtracting an appropriate multiple of n.
    // (n must be positive.)

    // This is often more useful than the built-in "%" operator,
    // which returns a result in the range (-n, n).

    ghost function int_mod(x: int, n: int): int
        requires n > int(0);
        ensures exists (k: int) x == k * n + return;
        ensures int(0) <= return < n;


    // Properties of "int_mod".

    ghost function mod_unique(x: int, n: int, k: int, r: int)
        requires n > int(0);
        requires x == k * n + r;
        requires int(0) <= r < n;
        ensures r == int_mod(x, n);

    ghost function mod_zero(k: int, n: int)
        requires n > int(0);
        ensures int_mod(k * n, n) == int(0);

    ghost function mod_add(x: int, y: int, n: int)
        requires n > int(0);
        ensures int_mod(x + y, n) == int_mod(int_mod(x, n) + y, n);

    ghost function mod_mul(x: int, y: int, n: int)
        requires n > int(0);
        ensures int_mod(x * y, n) == int_mod(int_mod(x, n) * y, n);


    // Implementations of "int_mod" for the built-in integer types.
    // Note: this is only provided for the signed integers, because
    // for unsigned integers, int_mod is equivalent to the built-in
    // "%" operator (see "int_mod_is_percent" below).

    function i8_mod(x: i8, y: i8): i8
        requires y > 0;
        ensures int(return) == int_mod(int(x), int(y));

    function i16_mod(x: i16, y: i16): i16
        requires y > 0;
        ensures int(return) == int_mod(int(x), int(y));

    function i32_mod(x: i32, y: i32): i32
        requires y > 0;
        ensures int(return) == int_mod(int(x), int(y));

    function i64_mod(x: i64, y: i64): i64
        requires y > 0;
        ensures int(return) == int_mod(int(x), int(y));


    //---------------------------------------------------------
    // Division (with remainder).

    // There are multiple ways to define integer division, but all
    // of them satisfy the following property.

    ghost function valid_division(x: int, y: int, q: int, r: int): bool
        requires y != int(0);
    {
        return x == q * y + r
            && int_abs(r) < int_abs(y);
    }


    //---------------------------------------------------------
    // Truncating division ("/" and "%").

    // This is built in to the language, but we can prove some
    // properties here.

    ghost function trunc_div_definition(x: int, y: int)
        requires y != int(0);
        ensures valid_division(x, y, x/y, x%y);
        ensures x%y == int(0) || int_sgn(x%y) == int_sgn(x);

    ghost function trunc_div_unique(x: int, y: int, q: int, r: int)
        requires y != int(0);
        requires valid_division(x, y, q, r);
        requires r == int(0) || int_sgn(r) == int_sgn(x);
        ensures q == x / y;
        ensures r == x % y;

    ghost function trunc_div_negate(x: int, y: int)
        requires y != int(0);
        ensures (-x) / (-y) == x / y;
        ensures (-x) / y == x / (-y) == - (x/y);
        ensures (-x) % y == - (x % y);
        ensures x % (-y) == x % y;


    //---------------------------------------------------------
    // Floor division.

    // This always rounds the quotient downwards (towards minus infinity).

    // The function returns both the quotient and the remainder.

    ghost function int_floor_div(x: int, y: int): {quot: int, rem: int}
        requires y != int(0);
        ensures valid_division(x, y, return.quot, return.rem);
        ensures return.rem == int(0) || int_sgn(return.rem) == int_sgn(y);


    // Properties of floor division.

    ghost function floor_div_unique(x: int, y: int, q: int, r: int)
        requires y != int(0);
        requires valid_division(x, y, q, r);
        requires r == int(0) || int_sgn(r) == int_sgn(y);
        ensures q == int_floor_div(x, y).quot;
        ensures r == int_floor_div(x, y).rem;

    ghost function floor_div_negate(x: int, y: int)
        requires y != int(0);
        ensures int_floor_div(-x, -y).quot == int_floor_div(x, y).quot;
        ensures int_floor_div(-x, -y).rem  == - int_floor_div(x, y).rem;

    ghost function floor_div_periodic(x: int, y: int, k: int)
        requires y != int(0);
        ensures int_floor_div(x + k * y, y).rem == int_floor_div(x, y).rem;


    // Implementations of floor division for the built-in signed integer
    // types. (Note that for unsigned integers, floor division is
    // equivalent to the usual "/" and "%" operators; see "div_equiv"
    // below.)

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
        ensures valid_division(x, y, return.quot, return.rem);
        ensures return.rem == int(0) || int_sgn(return.rem) == - int_sgn(y);


    // Properties of ceiling division.

    ghost function ceil_div_unique(x: int, y: int, q: int, r: int)
        requires y != int(0);
        requires valid_division(x, y, q, r);
        requires r == int(0) || int_sgn(r) == - int_sgn(y);
        ensures q == int_ceil_div(x, y).quot;
        ensures r == int_ceil_div(x, y).rem;

    ghost function ceil_div_negate(x: int, y: int)
        requires y != int(0);
        ensures int_ceil_div(-x, -y).quot == int_ceil_div(x, y).quot;
        ensures int_ceil_div(-x, -y).rem == - int_ceil_div(x, y).rem;

    ghost function ceil_div_periodic(x: int, y: int, k: int)
        requires y != int(0);
        ensures int_ceil_div(x + k * y, y).rem == int_ceil_div(x, y).rem;


    // Implementations of ceiling division for all eight integer types.

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

    // Note: For unsigned ceiling division, the remainder is always
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


    //---------------------------------------------------------
    // Euclidean division.

    // This always yields a non-negative remainder.

    // For positive divisors this is the same as floor division (see
    // "floor_euclid_div_equiv" below), but it behaves differently for
    // negative divisors.

    ghost function int_euclid_div(x: int, y: int): {quot: int, rem: int}
        requires y != int(0);
        ensures valid_division(x, y, return.quot, return.rem);
        ensures return.rem >= int(0);


    // Properties of Euclidean division.

    ghost function euclid_div_unique(x: int, y: int, q: int, r: int)
        requires y != int(0);
        requires valid_division(x, y, q, r);
        requires r >= int(0);
        ensures q == int_euclid_div(x, y).quot;
        ensures r == int_euclid_div(x, y).rem;

    ghost function euclid_div_negate(x: int, y: int)
        requires y != int(0);
        ensures int_euclid_div(x, -y).quot == - int_euclid_div(x, y).quot;
        ensures int_euclid_div(x, -y).rem == int_euclid_div(x, y).rem;

    ghost function euclid_div_periodic(x: int, y: int, k: int)
        requires y != int(0);
        ensures int_euclid_div(x + k * y, y).rem == int_euclid_div(x, y).rem;


    // Implementations of Euclidean division for the four signed
    // integer types. (Note that for unsigned integers, Euclidean
    // division is equivalent to the usual "/" and "%" operators.)

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
    // Equivalences between the different forms of division.

    // If x >= 0 and y > 0, then truncating, floor and Euclidean
    // division are all equivalent.

    ghost function div_equiv(x: int, y: int)
        requires x >= int(0);
        requires y > int(0);
        ensures {quot = x/y, rem = x%y} == int_floor_div(x, y) == int_euclid_div(x, y);

    // If y > 0 then floor and Euclidean division are equivalent.

    ghost function floor_euclid_div_equiv(x: int, y: int)
        requires y > int(0);
        ensures int_floor_div(x, y) == int_euclid_div(x, y);

    // The "int_mod" function is equivalent to the remainder of either
    // floor or Euclidean division. Also, if x >= 0, it is equivalent
    // to the built-in "%" operator.

    ghost function int_mod_is_floor_rem(x: int, y: int)
        requires y > int(0);
        ensures int_mod(x, y) == int_floor_div(x, y).rem;

    ghost function int_mod_is_euclid_rem(x: int, y: int)
        requires y > int(0);
        ensures int_mod(x, y) == int_euclid_div(x, y).rem;

    ghost function int_mod_is_percent(x: int, y: int)
        requires x >= int(0);
        requires y > int(0);
        ensures int_mod(x, y) == x % y;

}


// Implementation.

// "Modulo" functions.

ghost function int_mod(x: int, n: int): int
    requires n > int(0);
    ensures exists (k: int) x == k * n + return;
    ensures int(0) <= return < n;
{
    var r = x % n;
    if r < int(0) {
        assert exists (k: int) x == k * n + r + n {
            use x/n - int(1);
        }
        return r + n;
    } else {
        assert exists (k: int) x == k * n + r {
            use x/n;
        }
        return r;
    }
}

ghost function mod_unique(x: int, n: int, k: int, r: int)
    requires n > int(0);
    requires x == k * n + r;
    requires int(0) <= r < n;
    ensures r == int_mod(x, n);
{
    int_mod_is_floor_rem(x, n);
    floor_div_unique(x, n, k, r);
}

ghost function mod_zero(k: int, n: int)
    requires n > int(0);
    ensures int_mod(k * n, n) == int(0);
{}

ghost function mod_add(x: int, y: int, n: int)
    requires n > int(0);
    ensures int_mod(x + y, n) == int_mod(int_mod(x, n) + y, n);
{
    var r1 = int_mod(x + y, n);
    obtain (k1: int) x + y == k1 * n + r1;

    var r2 = int_mod(x, n);
    obtain (k2: int) x == k2 * n + r2;

    var r3 = int_mod(r2 + y, n);
    obtain (k3: int) r2 + y == k3 * n + r3;

    assert x + y == (k2 + k3) * n + r3;
    mod_unique(x + y, n, k2 + k3, r3);   // proves r3 == r1
}

ghost function mod_mul(x: int, y: int, n: int)
    requires n > int(0);
    ensures int_mod(x * y, n) == int_mod(int_mod(x, n) * y, n);
{
    var r1 = int_mod(x * y, n);
    obtain (k1: int) x * y == k1 * n + r1;

    var r2 = int_mod(x, n);
    obtain (k2: int) x == k2 * n + r2;

    var r3 = int_mod(r2 * y, n);
    obtain (k3: int) r2 * y == k3 * n + r3;

    assert x * y == k2 * y * n + k3 * n + r3;
    mod_unique(x * y, n, k2 * y + k3, r3);   // proves r3 == r1
}

function i8_mod(x: i8, y: i8): i8
    requires y > 0;
    ensures int(return) == int_mod(int(x), int(y));
{
    var r = x % y;
    if r < 0 {
        return r + y;
    } else {
        return r;
    }
}

function i16_mod(x: i16, y: i16): i16
    requires y > 0;
    ensures int(return) == int_mod(int(x), int(y));
{
    var r = x % y;
    if r < 0 {
        return r + y;
    } else {
        return r;
    }
}

function i32_mod(x: i32, y: i32): i32
    requires y > 0;
    ensures int(return) == int_mod(int(x), int(y));
{
    var r = x % y;
    if r < 0 {
        return r + y;
    } else {
        return r;
    }
}

function i64_mod(x: i64, y: i64): i64
    requires y > 0;
    ensures int(return) == int_mod(int(x), int(y));
{
    var r = x % y;
    if r < 0 {
        return r + y;
    } else {
        return r;
    }
}


// Truncating division.

ghost function trunc_div_definition(x: int, y: int)
    requires y != int(0);
    ensures valid_division(x, y, x/y, x%y);
    ensures x%y == int(0) || int_sgn(x%y) == int_sgn(x);
{}

ghost function trunc_div_unique(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires valid_division(x, y, q, r);
    requires r == int(0) || int_sgn(r) == int_sgn(x);
    ensures q == x / y;
    ensures r == x % y;
{}

ghost function trunc_div_negate(x: int, y: int)
    requires y != int(0);
    ensures (-x) / (-y) == x / y;
    ensures (-x) / y == x / (-y) == - (x/y);
    ensures (-x) % y == - (x % y);
    ensures x % (-y) == x % y;
{
    assert x == (x / y) * y + x % y;
    assert x == (x / (-y)) * (-y) + x % (-y);
}


// Floor division.

ghost function int_floor_div(x: int, y: int): {quot: int, rem: int}
    requires y != int(0);
    ensures valid_division(x, y, return.quot, return.rem);
    ensures return.rem == int(0) || int_sgn(return.rem) == int_sgn(y);
{
    var q = x / y;
    var r = x % y;
    if r < int(0) && y > int(0) || r > int(0) && y < int(0) {
        return { quot = q - int(1), rem = r + y };
    } else {
        return { quot = q, rem = r };
    }
}

ghost function floor_div_unique(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires valid_division(x, y, q, r);
    requires r == int(0) || int_sgn(r) == int_sgn(y);
    ensures q == int_floor_div(x, y).quot;
    ensures r == int_floor_div(x, y).rem;
{
    // This can most easily be expressed in terms of euclid_div_unique
    if y >= int(0) || r == int(0) {
        euclid_div_unique(x, y, q, r);
    } else {
        euclid_div_unique(x, y, q + int(1), r - y);
    }
}

ghost function floor_div_negate(x: int, y: int)
    requires y != int(0);
    ensures int_floor_div(-x, -y).quot == int_floor_div(x, y).quot;
    ensures int_floor_div(-x, -y).rem  == - int_floor_div(x, y).rem;
{
    var div = int_floor_div(x, y);
    assert x == div.quot * y + div.rem;
    assert -x == div.quot * (-y) - div.rem;
    floor_div_unique(-x, -y, div.quot, -div.rem);
}

ghost function floor_div_periodic(x: int, y: int, k: int)
    requires y != int(0);
    ensures int_floor_div(x + k * y, y).rem == int_floor_div(x, y).rem;
{
    var div = int_floor_div(x, y);
    assert x == div.quot * y + div.rem;
    assert x + k * y == (div.quot + k) * y + div.rem;
    floor_div_unique(x + k * y, y, div.quot + k, div.rem);
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
    ensures valid_division(x, y, return.quot, return.rem);
    ensures return.rem == int(0) || int_sgn(return.rem) == - int_sgn(y);
{
    var q = x / y;
    var r = x % y;
    if r < int(0) && y < int(0) || r > int(0) && y > int(0) {
        return { quot = q + int(1), rem = r - y };
    } else {
        return { quot = q, rem = r };
    }
}

ghost function ceil_div_unique(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires valid_division(x, y, q, r);
    requires r == int(0) || int_sgn(r) == - int_sgn(y);
    ensures q == int_ceil_div(x, y).quot;
    ensures r == int_ceil_div(x, y).rem;
{
    if r == int(0) {
        floor_div_unique(x, y, q, r);
    } else {
        floor_div_unique(x, y, q - int(1), r + y);
    }
}

ghost function ceil_div_negate(x: int, y: int)
    requires y != int(0);
    ensures int_ceil_div(-x, -y).quot == int_ceil_div(x, y).quot;
    ensures int_ceil_div(-x, -y).rem == - int_ceil_div(x, y).rem;
{
    var div = int_ceil_div(x, y);
    assert x == div.quot * y + div.rem;
    assert -x == div.quot * (-y) - div.rem;
    ceil_div_unique(-x, -y, div.quot, -div.rem);
}

ghost function ceil_div_periodic(x: int, y: int, k: int)
    requires y != int(0);
    ensures int_ceil_div(x + k * y, y).rem == int_ceil_div(x, y).rem;
{
    var div = int_ceil_div(x, y);
    assert x == div.quot * y + div.rem;
    assert x + k * y == (div.quot + k) * y + div.rem;
    ceil_div_unique(x + k * y, y, div.quot + k, div.rem);
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


// Euclidean division.

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

// Lemma for proving euclid_div_unique:
ghost function division_uniqueness(x: int, y: int, q1: int, r1: int, q2: int, r2: int)
    requires y != int(0);
    requires valid_division(x, y, q1, r1);
    requires valid_division(x, y, q2, r2);
    requires r1 >= int(0);
    requires r2 >= int(0);
    ensures q1 == q2;
    ensures r1 == r2;
{
    assert q1 == q2;   // z3 can solve this automatically
    assert r1 == x - q1 * y;  // because valid_division(x, y, q1, r1)
    assert r2 == x - q2 * y;  // because valid_division(x, y, q2, r2)
    assert r1 == r2;   // follows from previous three lines
}

ghost function euclid_div_unique(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires valid_division(x, y, q, r);
    requires r >= int(0);
    ensures q == int_euclid_div(x, y).quot;
    ensures r == int_euclid_div(x, y).rem;
{
    var div = int_euclid_div(x, y);
    division_uniqueness(x, y, div.quot, div.rem, q, r);
}

ghost function euclid_div_negate(x: int, y: int)
    requires y != int(0);
    ensures int_euclid_div(x, -y).quot == - int_euclid_div(x, y).quot;
    ensures int_euclid_div(x, -y).rem == int_euclid_div(x, y).rem;
{
    var div = int_euclid_div(x, y);
    assert x == div.quot * y + div.rem;
    assert x == (-div.quot) * (-y) + div.rem;
    euclid_div_unique(x, -y, -div.quot, div.rem);
}

ghost function euclid_div_periodic(x: int, y: int, k: int)
    requires y != int(0);
    ensures int_euclid_div(x + k * y, y).rem == int_euclid_div(x, y).rem;
{
    var div = int_euclid_div(x, y);
    assert x == div.quot * y + div.rem;
    assert x + k * y == (div.quot + k) * y + div.rem;
    euclid_div_unique(x + k * y, y, div.quot + k, div.rem);
}

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


// Equivalence theorems.

ghost function div_equiv(x: int, y: int)
    requires x >= int(0);
    requires y > int(0);
    ensures {quot = x/y, rem = x%y} == int_floor_div(x, y) == int_euclid_div(x, y);
{}

ghost function floor_euclid_div_equiv(x: int, y: int)
    requires y > int(0);
    ensures int_floor_div(x, y) == int_euclid_div(x, y);
{}

ghost function int_mod_is_floor_rem(x: int, y: int)
    requires y > int(0);
    ensures int_mod(x, y) == int_floor_div(x, y).rem;
{}

ghost function int_mod_is_euclid_rem(x: int, y: int)
    requires y > int(0);
    ensures int_mod(x, y) == int_euclid_div(x, y).rem;
{}

ghost function int_mod_is_percent(x: int, y: int)
    requires x >= int(0);
    requires y > int(0);
    ensures int_mod(x, y) == x % y;
{}
