module Strings
interface {}

function f1()
{
    assert (sizeof("ABC") == u64(4));
    assert ("ABC" [1] == 66);     // 66 = ascii 'B'
}

function f2()
{
    ref s = "ABC";
    ref t = s;
    assert (sizeof(t) == u64(4));
    assert (t[0] == 65);         // 65 = ascii 'A'
}

function f3()
{
    assert ("AAA"[0] == 10);   // Fails
}

function f4()
{
    assert (sizeof("AAA") == u64(1));  // Fails
}

function f5()
{
    // Escape codes
    ref r = "\x00\t\n\x01\xff\"\xAB";
    assert (r[0] == 0);
    assert (r[1] == 9);
    assert (r[2] == 10);
    assert (r[3] == 1);
    assert (r[4] == 255);
    assert (r[5] == 34);
    assert (r[6] == 171);
    assert (r[7] == 0);  // null terminator is added automatically (like in C)
    assert (sizeof(r) == u64(8));

    // More escape codes
    ref s = "\a\b\f\n\r\t\v\"\\\x10";
    assert s[0] == 7;
    assert s[1] == 8;
    assert s[2] == 12;
    assert s[3] == 10;
    assert s[4] == 13;
    assert s[5] == 9;
    assert s[6] == 11;
    assert s[7] == 34;
    assert s[8] == 92;
    assert s[9] == 16;
    assert s[10] == 0;
    assert sizeof(s) == 11;

    assert s[0] == 1; // Error
}

function big_string()
{
    ref r = "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890";
    assert(sizeof(r) == u64(301));
    assert(r[100] == 49);   // 49 = ascii '1'
}


// This generates an axiom something like
// valid(s) ==> return_42(s) == 42,
// where valid(s) says (among other things) that s[i] == $ARBITRARY for i >= sizeof(s).
function return_42(s: u8[]): i32
{
    return 42;
}

// The assert in this function will only work if valid(s) is added to the assumptions.
// Therefore this is (effectively) a test that the validity condition is being added
// for string constants.
function test_42()
{
    ref s = "Hello";
    assert return_42(s) == 42;
}
