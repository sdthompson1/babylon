module String

// Some functions for working with null-terminated strings.

// We make no assumptions about the character set, except in the string/integer
// conversion functions, where ASCII is assumed.

import Maybe;
import Ord;

interface {

    // ** Valid-string predicate

    // A u8 buffer is a "valid string" if it contains a null byte somewhere
    // within it.
    ghost function valid_string(s: u8[]): bool
    {
        return exists (j: u64) j < sizeof(s) && s[j] == 0;
    }

    // This lemma is often needed to help the solver prove the
    // "exists" clause in valid_string.
    ghost function valid_string_lemma(s: u8[], idx: u64)
        requires idx < sizeof(s);
        requires s[idx] == 0;
        ensures valid_string(s);
    {}


    // ** String length
    
    function strlen(s: u8[]): u64
        requires valid_string(s);
        ensures return < sizeof(s) &&
            s[return] == 0 &&
            forall (j:u64) j < return ==> s[j] != 0;


    // ** String comparison

    // Helper functions for string comparison spec:

    // True if first n bytes of s1 and s2 are equal
    ghost function first_n_equal(s1: u8[], s2: u8[], n: u64): bool
        requires valid_string(s1);
        requires valid_string(s2);
        requires n <= strlen(s1);
        requires n <= strlen(s2);
    {
        return forall (j:u64) j < n ==> s1[j] == s2[j];
    }

    // True if s1 is less than s2, with the "first difference" at position n
    ghost function string_less_witness(s1: u8[], s2: u8[], n: u64): bool
        requires valid_string(s1);
        requires valid_string(s2);
    {
        if n > strlen(s1) || n > strlen(s2) || !first_n_equal(s1, s2, n) {
            return false;
        } else if strlen(s2) == n {
            return false;  // either s1=s2 or s1>s2
        } else if strlen(s1) == n {
            return true;   // s1 is a (strict) prefix of s2
        } else {
            return s1[n] < s2[n];
        }
    }

    // The strcmp function itself:

    function strcmp(s1: u8[], s2: u8[]): Ordering
        requires valid_string(s1);
        requires valid_string(s2);
        ensures return == EQ <==>
            strlen(s1) == strlen(s2)
            && first_n_equal(s1, s2, strlen(s1));
        ensures return == LT <==>
            exists (n: u64) string_less_witness(s1, s2, n);
        ensures return == GT <==>
            exists (n: u64) string_less_witness(s2, s1, n);


    // ** String searching

    // Search forwards for a given byte value, starting from the given position
    function strchr(str: u8[], to_find: u8, start: u64): Maybe<u64>
        requires valid_string(str);
        requires start <= strlen(str);
        ensures match return {
            case Nothing =>
                forall (j: u64) start <= j < strlen(str) ==> str[j] != to_find;
            case Just(pos) =>
                start <= pos < strlen(str)
                && (forall (j: u64) start <= j < pos ==> str[j] != to_find)
                && str[pos] == to_find
            };

    // Search backwards for a given byte value, starting one place to the left of
    // the given position
    function strrchr(str: u8[], to_find: u8, start: u64): Maybe<u64>
        requires valid_string(str);
        requires start <= strlen(str);
        ensures match return {
            case Nothing =>
                forall (j: u64) j < start ==> str[j] != to_find;
            case Just(pos) =>
                pos < start
                && (forall (j: u64) pos < j < start ==> str[j] != to_find)
                && str[pos] == to_find
            };

    // Spec function for strstr
    ghost function strstr_witness(str: u8[], to_find: u8[], pos: u64): bool
        requires valid_string(str);
        requires valid_string(to_find);
    {
        return int(pos) <= int(strlen(str)) - int(strlen(to_find))
            && forall (j: u64) j < strlen(to_find) ==> str[pos + j] == to_find[j];
    }

    // Search for a substring, starting from the given position
    function strstr(str: u8[], to_find: u8[], start: u64): Maybe<u64>
        requires valid_string(str);
        requires valid_string(to_find);
        requires start <= strlen(str);
        ensures match return {
            case Nothing =>
                !exists (pos: u64) pos >= start && strstr_witness(str, to_find, pos);
            case Just(pos) =>
                pos >= start
                && strstr_witness(str, to_find, pos)
                && forall (j: u64) start <= j < pos ==> !strstr_witness(str, to_find, j);
        };


    // ** Copying strings

    // Copy a string
    function strcpy(ref dest: u8[], src: u8[])
        requires valid_string(src);
        requires strlen(src) < sizeof(dest);
        ensures valid_string(dest);
        ensures sizeof(dest) == old(sizeof(dest));
        ensures forall (j: u64) j <= strlen(src) ==> dest[j] == src[j];

    // Copy a string, truncating to fit in the destination if necessary.
    function strcpy_trunc(ref dest: u8[], src: u8[])
        requires valid_string(src);
        requires sizeof(dest) >= 1;
        ensures valid_string(dest);
        ensures sizeof(dest) == old(sizeof(dest));
        ensures forall (j: u64)
            j <= strlen(src) && j < sizeof(dest) - 1 ==>
                dest[j] == src[j];


    // ** Concatenating strings

    // Append the src string to the dest string.
    function strcat(ref dest: u8[], src: u8[])
        requires valid_string(src);
        requires valid_string(dest);
        requires int(strlen(src)) + int(strlen(dest)) < int(sizeof(dest));
        ensures valid_string(dest);
        ensures sizeof(dest) == old(sizeof(dest));
        ensures forall (j: u64) j < old(strlen(dest)) ==>
            dest[j] == old(dest[j]);
        ensures forall (j: u64) j <= strlen(src) ==>
            dest[old(strlen(dest)) + j] == src[j];

    // Append strings, truncating to fit the destination if necessary.
    function strcat_trunc(ref dest: u8[], src: u8[])
        requires valid_string(src);
        requires valid_string(dest);
        ensures valid_string(dest);
        ensures sizeof(dest) == old(sizeof(dest));
        ensures forall (j: u64) j < old(strlen(dest)) ==>
            dest[j] == old(dest[j]);
        ensures forall (j: u64) j <= strlen(src)
            && int(old(strlen(dest))) + int(j) < int(sizeof(dest) - 1) ==>
                dest[old(strlen(dest)) + j] == src[j];


    // ** Integer/string conversion

    function string_to_i64(str: u8[]): Maybe<i64>;
        requires valid_string(str);

    function string_to_u64(str: u8[]): Maybe<u64>;
        requires valid_string(str);

    function i64_to_string(num: i64, ref str: u8[]);
        requires sizeof(str) >= 21;
        ensures sizeof(str) == old(sizeof(str));
        ensures valid_string(str);

    function u64_to_string(num: u64, ref str: u8[]);
        requires sizeof(str) >= 21;
        ensures sizeof(str) == old(sizeof(str));
        ensures valid_string(str);
}

import Ascii;
import Int;

function strlen(s: u8[]): u64
    requires valid_string(s);
    ensures return < sizeof(s) &&
        s[return] == 0 &&
        forall (j:u64) j < return ==> s[j] != 0;
{
    var i: u64 = 0;
    while true
        invariant i < sizeof(s);
        invariant forall (j: u64) j < i ==> s[j] != 0;
        decreases ~i;
    {
        if s[i] == 0 {
            return i;
        }
        i = i + u64(1);
    }
}

function strcmp(s1: u8[], s2: u8[]): Ordering
    requires valid_string(s1);
    requires valid_string(s2);
    ensures return == EQ <==>
        strlen(s1) == strlen(s2)
        && first_n_equal(s1, s2, strlen(s1));
    ensures return == LT <==>
        exists (n: u64) string_less_witness(s1, s2, n);
    ensures return == GT <==>
        exists (n: u64) string_less_witness(s2, s1, n);
{
    var i: u64 = 0;
    while true
        invariant i <= strlen(s1);
        invariant i <= strlen(s2);
        invariant first_n_equal(s1, s2, i);
        decreases ~i;
    {
        var left = s1[i];
        var right = s2[i];
        if left == 0 {
            if right == 0 {
                return EQ;
            } else {
                return LT;
            }
        } else if right == 0 {
            return GT;
        } else if left > right {
            return GT;
        } else if left < right {
            return LT;
        }
        i = i + 1;
    }
}

function strchr(str: u8[], to_find: u8, start: u64): Maybe<u64>
    requires valid_string(str);
    requires start <= strlen(str);
    ensures match return {
        case Nothing =>
            forall (j: u64) start <= j < strlen(str) ==> str[j] != to_find;
        case Just(pos) =>
            start <= pos < strlen(str)
            && (forall (j: u64) start <= j < pos ==> str[j] != to_find)
            && str[pos] == to_find
        };
{
    var i: u64 = start;
    while true
        invariant start <= i <= strlen(str);
        invariant forall (j: u64) start <= j < i ==> str[j] != to_find;
        decreases ~i;
    {
        var byte = str[i];
        if byte == 0 {
            return Nothing;
        } else if byte == to_find {
            return Just(i);
        }
        i = i + 1;
    }
}

function strrchr(str: u8[], to_find: u8, start: u64): Maybe<u64>
    requires valid_string(str);
    requires start <= strlen(str);
    ensures match return {
        case Nothing =>
            forall (j: u64) j < start ==> str[j] != to_find;
        case Just(pos) =>
            pos < start
            && (forall (j: u64) pos < j < start ==> str[j] != to_find)
            && str[pos] == to_find
        };
{
    var i: u64 = start;
    while true
        invariant i <= start;
        invariant forall (j: u64) i <= j < start ==> str[j] != to_find;
        decreases i;
    {
        if i == 0 {
            return Nothing;
        }
        i = i - 1;
        if str[i] == to_find {
            return Just(i);
        }
    }
}

function strstr_helper(str: u8[], to_find: u8[], pos: u64): bool
    requires valid_string(str);
    requires valid_string(to_find);
    requires pos <= strlen(str);
    ensures return <==> strstr_witness(str, to_find, pos);
{
    var i: u64 = 0;
    while to_find[i] != 0
        invariant int(pos) + int(i) <= int(strlen(str));
        invariant i <= strlen(to_find);
        invariant forall (j: u64) j < i ==> str[pos + j] == to_find[j];
        decreases ~i;
    {
        if str[pos + i] != to_find[i] {
            return false;
        }
        i = i + 1;
    }
    return true;
}

function strstr(str: u8[], to_find: u8[], start: u64): Maybe<u64>
    requires valid_string(str);
    requires valid_string(to_find);
    requires start <= strlen(str);
    ensures match return {
        case Nothing =>
            !exists (pos: u64) pos >= start && strstr_witness(str, to_find, pos);
        case Just(pos) =>
            pos >= start
            && strstr_witness(str, to_find, pos)
            && forall (j: u64) start <= j < pos ==> !strstr_witness(str, to_find, j);
    };
{
    // TODO: Maybe we could implement (and verify) a more efficient algorithm, e.g.
    // the "two way" algorithm: https://en.wikipedia.org/wiki/Two-way_string-matching_algorithm.
    // However, the naive implementation given below should work well enough for short strings
    // at least.
    var pos: u64 = start;
    while true
        invariant start <= pos <= strlen(str);
        invariant forall (j: u64) start <= j < pos ==> !strstr_witness(str, to_find, j);
        decreases ~pos;
    {
        if strstr_helper(str, to_find, pos) {
            hide strstr_witness;
            return Just(pos);
        }
        if str[pos] == 0 {
            // reached end of str, so result cannot be 'pos' or greater
            assert forall (j: u64) j >= pos ==> !strstr_witness(str, to_find, j);
            hide strstr_witness;
            return Nothing;
        }
        assert !strstr_witness(str, to_find, pos);
        pos = pos + 1;
        hide strstr_witness;
    }
}

function strcpy(ref dest: u8[], src: u8[])
    requires valid_string(src);
    requires strlen(src) < sizeof(dest);
    ensures valid_string(dest);
    ensures sizeof(dest) == old(sizeof(dest));
    ensures forall (j: u64) j <= strlen(src) ==> dest[j] == src[j];
{
    ghost var buf_size = sizeof(dest);

    var pos: u64 = 0;
    while true
        invariant sizeof(dest) == buf_size;
        invariant pos <= strlen(src);
        invariant forall (j: u64) j < pos ==> dest[j] == src[j];
        decreases ~pos;
    {
        dest[pos] = src[pos];
        if src[pos] == 0 {
            return;
        }
        pos = pos + 1;
    }
}    

function strcpy_trunc(ref dest: u8[], src: u8[])
    requires valid_string(src);
    requires sizeof(dest) >= 1;
    ensures valid_string(dest);
    ensures sizeof(dest) == old(sizeof(dest));
    ensures forall (j: u64)
        j <= strlen(src) && j < sizeof(dest) - 1 ==>
            dest[j] == src[j];
{
    var buf_size: u64 = sizeof(dest);

    var pos: u64 = 0;
    while pos < buf_size - 1
        invariant sizeof(dest) == buf_size;
        invariant pos <= strlen(src);
        invariant pos < buf_size;
        invariant forall (j: u64) j < pos ==> dest[j] == src[j];
        decreases ~pos;
    {
        dest[pos] = src[pos];
        if src[pos] == 0 {
            return;
        }
        pos = pos + 1;
    }

    // truncation case
    dest[pos] = 0;
}    

function strcat(ref dest: u8[], src: u8[])
    requires valid_string(src);
    requires valid_string(dest);
    requires int(strlen(src)) + int(strlen(dest)) < int(sizeof(dest));
    ensures valid_string(dest);
    ensures sizeof(dest) == old(sizeof(dest));
    ensures forall (j: u64) j < old(strlen(dest)) ==>
        dest[j] == old(dest[j]);
    ensures forall (j: u64) j <= strlen(src) ==>
        dest[old(strlen(dest)) + j] == src[j];
{
    ghost var old_dest = dest;

    var base: u64 = strlen(dest);
    var idx: u64 = 0;

    while true
        invariant sizeof(dest) == sizeof(old_dest);
        invariant idx <= strlen(src);
        invariant forall (j: u64) j < base ==> dest[j] == old_dest[j];
        invariant forall (j: u64) j < idx ==> dest[base + j] == src[j];
        decreases ~idx;
    {
        dest[base + idx] = src[idx];
        if src[idx] == 0 {
            return;
        }
        idx = idx + 1;
    }
}

function strcat_trunc(ref dest: u8[], src: u8[])
    requires valid_string(src);
    requires valid_string(dest);
    ensures valid_string(dest);
    ensures sizeof(dest) == old(sizeof(dest));
    ensures forall (j: u64) j < old(strlen(dest)) ==>
        dest[j] == old(dest[j]);
    ensures forall (j: u64) j <= strlen(src)
        && int(old(strlen(dest))) + int(j) < int(sizeof(dest) - 1) ==>
            dest[old(strlen(dest)) + j] == src[j];
{
    ghost var old_dest = dest;

    var buf_size: u64 = sizeof(dest);

    var base: u64 = strlen(dest);
    var idx: u64 = 0;

    while base + idx < buf_size - 1
        invariant sizeof(dest) == buf_size;
        invariant idx <= strlen(src);
        invariant int(base) + int(idx) < int(buf_size);
        invariant forall (j: u64) j < base ==> dest[j] == old_dest[j];
        invariant forall (j: u64) j < idx ==> dest[base + j] == src[j];
        decreases ~idx;
    {
        dest[base + idx] = src[idx];
        if src[idx] == 0 {
            return;
        }
        idx = idx + 1;
    }

    // truncation case
    dest[base + idx] = 0;
}

// Private function. The bool is a "sign bit" and the u64 is the number.
function string_to_integer(str: u8[]): Maybe<{bool, u64}>
    requires valid_string(str);
{
    // Skip any leading whitespace
    var i: u64 = 0;
    while str[i] != 0 && isspace(str[i])
        invariant i <= strlen(str);
        decreases ~i;
    {
        i = i + 1;
    }

    // Skip a single plus or minus character
    var minus = false;
    if str[i] == 43 {   // ascii '+'
        i = i + 1;
    } else if str[i] == 45 {    // ascii '-'
        i = i + 1;
        minus = true;
    }

    // Read digit characters
    var number: u64 = 0;
    while str[i] != 0 && !isspace(str[i])
        invariant i <= strlen(str);
        decreases ~i;
    {
        if 48 <= str[i] <= 57 {         // 48 = ascii '0'; 57 = ascii '9'
            var d = str[i] - 48;

            var too_big = (number > (U64_MAX - d)/10);
            assert too_big <==> int(number) * int(10) + int(d) > int(U64_MAX);

            if too_big {
                return Nothing;  // Too big for u64
            }

            number = number * 10 + d;
            i = i + 1;

        } else {
            return Nothing;   // non-digit character found
        }
    }

    // Skip any trailing whitespace
    while str[i] != 0 && isspace(str[i])
        invariant i <= strlen(str);
        decreases ~i;
    {
        i = i + 1;
    }

    if str[i] != 0 {
        return Nothing;   // found invalid character(s) after the number
    } else {
        return Just {minus, number};
    }
}

function string_to_i64(str: u8[]): Maybe<i64>
    requires valid_string(str);
{
    match string_to_integer(str) {
    case Nothing =>
        return Nothing;

    case Just{true, num} =>
        // Negative number
        if num > u64(I64_MAX) + u64(1) {
            assert -int(num) < int(I64_MIN);
            return Nothing;
        } else if num == u64(I64_MAX) + u64(1) {
            assert -int(num) == int(I64_MIN);
            return Just(I64_MIN);
        } else {
            return Just(-i64(num));
        }

    case Just{false, num} =>
        // Positive number
        if num > u64(I64_MAX) {
            return Nothing;
        } else {
            return Just(i64(num));
        }
    }
}

function string_to_u64(str: u8[]): Maybe<u64>
    requires valid_string(str);
{
    match string_to_integer(str) {
    case Nothing =>
        return Nothing;
    case Just{true, _} =>
        return Nothing;  // negative number
    case Just{false, num} =>
        return Just(num);
    }
}

// Private function.
function integer_to_string(sign: bool, num: u64, ref str: u8[])
    requires sizeof(str) >= 21;   // 20 u64 digits + null byte (or minus sign + 19 i64 digits + null).
    requires sign ==> num <= u64(I64_MAX) + 1;
    ensures sizeof(str) == old(sizeof(str));
    ensures valid_string(str);
{
    ghost var size = sizeof(str);

    var i: u8 = 0;
    var number: u64 = num;

    // Handle the special case of zero.
    if num == 0 {
        str[0] = 48;    // ascii '0'
        str[1] = 0;
        return;
    }
    
    // Write initial minus sign if required.
    if sign {
        str[0] = 45;    // ascii '-'
        i = 1;
    } 

    // Write the digits of 'number' in reverse order.
    var j = i;
    while j < 20 && number > 0
        invariant i <= j <= 20;
        invariant sizeof(str) == size;
        invariant forall (k: u8) k < j ==> str[k] != 0;
        decreases ~j;
    {
        str[j] = (number % 10) + 48;  // 48 = ascii '0'
        number = number / 10;
        j = j + 1;
    }

    // Write a null terminator at position j.
    str[j] = 0;
    assert strlen(str) == j;

    // Reverse the digits in the range [i,j).
    while i + 1 < j
        invariant valid_string(str);
        invariant i <= j <= strlen(str);
        invariant sizeof(str) == size;
        decreases ~i;
    {
        swap str[i], str[j - 1];
        i = i + 1;
        j = j - 1;
    }
}

function i64_to_string(num: i64, ref str: u8[])
    requires sizeof(str) >= 21;
    ensures sizeof(str) == old(sizeof(str));
    ensures valid_string(str);
{
    if num >= 0 {
        integer_to_string(false, num, str);
    } else if num == I64_MIN {
        assert -int(num) == int(I64_MAX) + int(1);
        integer_to_string(true, u64(I64_MAX) + 1, str);
    } else {
        integer_to_string(true, -num, str);
    }
    hide valid_string;
}

function u64_to_string(num: u64, ref str: u8[])
    requires sizeof(str) >= 21;
    ensures sizeof(str) == old(sizeof(str));
    ensures valid_string(str);
{
    integer_to_string(false, num, str);
}
