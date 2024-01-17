module Main

interface {}

import Default;

ghost function test()
{
    // This is testing that even though we don't know the implementation of
    // "default<T>", we do know that the value returned is a valid "T",
    // for any type T.
    
    ghost var x: u8 = default<u8>();
    assert 0 <= x <= 255;

    ghost var y: {i16, i8} = default<{i16, i8}>();
    assert -32768 <= y.0 <= 32767;
    assert -128 <= y.1 <= 127;

    // This next assert should fail -- even though default<T> does actually return
    // zero, we do not know this because the implementation is hidden.
    assert y.1 == 0;
}
