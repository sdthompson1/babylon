module Obtain
interface {}


ghost function test()
{
    obtain (x:i32) x > 0;   // OK
    obtain (y:i32) y != y;  // Error

    assert x > 0;   // Should be true because of the obtain-condition

    x = -1;
    assert x > 0;   // Error, x has been overwritten
}

ghost function test2()
{
    obtain (z:i32) 1/0 == 0;    // Error, condition doesn't verify
}

ghost function test3()
{
    obtain (x: u8) x > u8(255);   // Error, no such x exists at type u8
}
