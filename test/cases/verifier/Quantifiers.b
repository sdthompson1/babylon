module Quantifiers
interface {}

  function f1()
  {
    assert (exists (x:i32) x == 0);     // True
    assert (forall (x:i32) x == 0);     // Not true
  }

  function f2()
  {
    assert (exists (x:i32) x == 1/0);   // Invalid, operator precondition failure
  }

  function f3(x: u8)
    requires forall (y:u8) x >= y;
  {
    assert (x == 255);                  // True (based on the precondition)
    assert (forall (y:i32) x >= y);     // Not true
  }
