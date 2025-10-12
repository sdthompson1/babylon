module Main

interface {}

import Test;

const str: u8[] = "Hello";

function byref(ref s: u8[])
{
}

function f1()
{
    ref r = "foo";     // Allowed, but r is considered a 'const' reference

    byref(str);        // error, can't pass 'str' by reference
    byref("string constant");  // error, can't pass a string literal by reference
    byref(r);          // error, can't write to const-ref

    str[0] = 35;        // error, can't write to 'str'
    ("test1")[0] = 35;  // error, can't write to string literal
    r[0] = 100;         // error, can't write to const-ref
}
