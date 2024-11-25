module Ascii

// Functions for working with ASCII codes.

// TODO: Some equivalent of this for Unicode. (Obviously it will be more complex
// in the Unicode case.)

interface {
    // True if 'c' is a valid ASCII code.
    function isascii(c: u8): bool
    {
        return c <= 127;
    }

    // True if 'c' is an alphanumeric character (A-Z, a-z, 0-9).
    function isalnum(c: u8): bool;

    // True if 'c' is an alphabetic character (A-Z, a-z).
    function isalpha(c: u8): bool;

    // True if 'c' is a control character (either c <= 31 or c == 127). Same as !isprint(c).
    function iscntrl(c: u8): bool;

    // True if 'c' is a decimal digit (0-9).
    function isdigit(c: u8): bool;

    // True if 'c' has a graphical representation. Same as isalnum(c) || ispunct(c).
    function isgraph(c: u8): bool;

    // True if 'c' is a lowercase letter (a-z).
    function islower(c: u8): bool;

    // True if 'c' is printable. Same as isgraph(c) || c == 32. Also same as !iscntrl(c).
    function isprint(c: u8): bool;

    // True if 'c' is punctuation, i.e. one of: !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
    function ispunct(c: u8): bool;

    // True if 'c' is whitespace (space, tab, newline, vertical tab, form feed or carriage return).
    function isspace(c: u8): bool;

    // True if 'c' is an uppercase letter (A-Z).
    function isupper(c: u8): bool;

    // True if 'c' is a hex digit (0-9, a-f or A-F).
    function isxdigit(c: u8): bool;

    // If 'c' is an uppercase letter, convert it to lowercase, otherwise leave it unchanged.
    function tolower(c: u8): u8;
        ensures isascii(c) ==> isascii(return);

    // If 'c' is a lowercase letter, convert it to uppercase, otherwise leave it unchanged.
    function toupper(c: u8): u8;
        ensures isascii(c) ==> isascii(return);
}

function isalnum(c: u8): bool
{
    return isalpha(c) || isdigit(c);
}

function isalpha(c: u8): bool
{
    return isupper(c) || islower(c);
}

function iscntrl(c: u8): bool
{
    return c <= 31 || c == 127;
}

function isdigit(c: u8): bool
{
    return 48 <= c <= 57;
}

function isgraph(c: u8): bool
{
    return 33 <= c <= 126;
}

function islower(c: u8): bool
{
    return 97 <= c <= 122;
}

function isprint(c: u8): bool
{
    return 32 <= c <= 126;
}

function ispunct(c: u8): bool
{
    return 33 <= c <= 47 || 58 <= c <= 64 || 91 <= c <= 96 || 123 <= c <= 126;
}

function isspace(c: u8): bool
{
    return 9 <= c <= 13 || c == 32;
}

function isupper(c: u8): bool
{
    return 65 <= c <= 90;
}

function isxdigit(c: u8): bool
{
    return 48 <= c <= 57 || 65 <= c <= 70 || 97 <= c <= 102;
}

function tolower(c: u8): u8;
    ensures isascii(c) ==> isascii(return);
{
    if isupper(c) {
        return c + 32;
    } else {
        return c;
    }
}

function toupper(c: u8): u8;
    ensures isascii(c) ==> isascii(return);
{
    if islower(c) {
        return c - 32;
    } else {
        return c;
    }
}

// Some properties, for "checking" purposes
ghost function properties(c: u8)
{
    assert isascii(c) <==> isprint(c) || iscntrl(c);
    assert !(isprint(c) && iscntrl(c));
    assert isalnum(c) <==> isalpha(c) || isdigit(c);
    assert isalpha(c) <==> isupper(c) || islower(c);
    assert isgraph(c) <==> isalnum(c) || ispunct(c);
    assert isprint(c) <==> isgraph(c) || c == 32;
    assert isspace(32);
    assert !isgraph(32);
    assert isprint(32);
    assert isspace(c) ==> c == 32 || iscntrl(c);
    assert isxdigit(c) ==> isalnum(c);
    assert isupper(c) ==> islower(tolower(c));
    assert !isupper(c) ==> tolower(c) == c;
    assert islower(c) ==> isupper(toupper(c));
    assert !islower(c) ==> toupper(c) == c;
}
