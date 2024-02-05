module Main

interface {}

import Imported;

function test1()
{
    ref s1: u8[] = "StringTest456";
    ref s2: u8[] = "StringTest123";
    assert s1 == STR;  // Should fail, strings are not equal.
    assert s2 == STR;  // Should succeed.
}
