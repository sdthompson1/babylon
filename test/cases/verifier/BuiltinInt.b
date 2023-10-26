module BuiltinInt
interface {}
  import Int;

  function test()
  {
    assert (Int.can_add_u8(200, 55));   // OK
    assert (Int.can_add_u8(200, 56));   // Error
  }

  function test2()
  {
    assert (Int.can_div_i32(100, 10));  // OK
    assert (Int.can_div_i32(100, 0));   // Error
  }
