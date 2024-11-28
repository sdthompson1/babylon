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
    // is any pair of integers such that x = q*y + r, then {q,r} is
    // equal to int_euclid_div(x,y).
    
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

// To prove int_euclid_div_unique we proceed by induction.

// The base case is when |x| < |y|, i.e. the quotient is zero.

ghost function int_euclid_div_unique_base_case(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires int_abs(x) < int_abs(y);
    requires x == q * y + r;
    requires int(0) <= r < int_abs(y);
    ensures {quot = q, rem = r} == int_euclid_div(x, y);
{
    assert x / y == int(0);
    if x >= int(0) {
        return;
    } else if y > int(0) {
        return;
    } else {
        return;
    }    
}

// Some lemmas needed for the inductive step.

ghost function mod_lemma_1(x: int, y: int)
    requires y > int(0);
    ensures (x + y) % y == x % y
        || (x + y) % y == x % y + y;
{
    if x == int(0) { return; }
    assert x > int(0) ==> int(0) <= x % y < int(y);
    assert x > int(0) ==> int(0) <= (x + y) % y < int(y);
    return;
}

ghost function mod_lemma_2(x: int, y: int)
    requires y < int(0);
    ensures (x + y) % y == x % y
        || (x + y) % y == x % y + y;
{}

ghost function mod_lemma_3(x: int, y: int)
    requires y > int(0);
    ensures (x - y) % y == x % y
        || (x - y) % y == x % y - y;
{
    if x == int(0) { return; }
    assert x > int(0) ==> int(0) <= x % y < int(y);
    assert x > int(0) ==> int(0) <= (x + y) % y < int(y);
    return;
}

ghost function mod_lemma_4(x: int, y: int)
    requires y < int(0);
    ensures (x - y) % y == x % y
        || (x - y) % y == x % y - y;
{}

// There are two inductive steps: one for increasing the quotient (induction upwards
// from zero) and one for reducing the quotient (induction downwards from zero).

ghost function int_euclid_div_step_up(x: int, y: int)
    requires y != int(0);
    ensures int_euclid_div(x + y, y).quot == int_euclid_div(x, y).quot + int(1);
    ensures int_euclid_div(x + y, y).rem == int_euclid_div(x, y).rem;
{
    if (x + y) % y == x % y {
        assert (x + y) / y == x / y + int(1);
        return;
    } else if y > int(0) {
        mod_lemma_1(x, y);
        return;
    } else {
        mod_lemma_2(x, y);
        return;
    }
}

ghost function int_euclid_div_step_down(x: int, y: int)
    requires y != int(0);
    ensures int_euclid_div(x - y, y).quot == int_euclid_div(x, y).quot - int(1);
    ensures int_euclid_div(x - y, y).rem == int_euclid_div(x, y).rem;
{
    if (x - y) % y == x % y {
        assert (x - y) / y == x / y - int(1);
        return;
    } else if y > int(0) {
        mod_lemma_3(x, y);
        return;
    } else {
        mod_lemma_4(x, y);
        return;
    }
}

// Now we can write the required induction proof as two while-loops
// (one going upwards from zero, and another going downwards from zero).

ghost function int_euclid_div_unique(x: int, y: int, q: int, r: int)
    requires y != int(0);
    requires x == q * y + r;
    requires int(0) <= r < int_abs(y);
    ensures {quot = q, rem = r} == int_euclid_div(x, y);
{
    var xx: int = r;
    var qq: int = int(0);

    int_euclid_div_unique_base_case(xx, y, qq, r);

    if q >= int(0) {
        // Step qq upwards towards q.
        while qq < q
            invariant qq <= q;
            invariant xx == qq * y + r;
            invariant {quot = qq, rem = r} == int_euclid_div(xx, y);
            decreases q - qq;
        {
            int_euclid_div_step_up(xx, y);
            xx = xx + y;
            qq = qq + int(1);
        }
    } else {
        // Step qq downwards towards q.
        while qq > q
            invariant qq >= q;
            invariant xx == qq * y + r;
            invariant {quot = qq, rem = r} == int_euclid_div(xx, y);
            decreases qq - q;
        {
            int_euclid_div_step_down(xx, y);
            xx = xx - y;
            qq = qq - int(1);
        }
    }
    hide int_euclid_div;
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
