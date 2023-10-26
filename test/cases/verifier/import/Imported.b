module Imported
interface {
  function foo(x: i32): i32
    requires x > 0;
}

  function foo(x: i32): i32
    requires x >= 0;
  {
    return 999;
  }
