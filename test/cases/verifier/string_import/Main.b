module Main

interface {}

import Imported;

function test1()
{
    ref s: u8[] = "StringTest456";
    assert s == STR;  // Should fail, strings are not equal.
}
