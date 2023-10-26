module InterfaceImpl
interface {
  function f1(x: i32);

  function f2(x: i32): i32
    ensures return == 100;

  function f3(x: i32): i32
    requires x > 0;
    ensures return < -10;

  function f4(x: i32): i32
    requires x < 0;
    ensures return >= 0;

  function f5(x: i32, y: i32)
    requires x > 0;
    requires y > 3;

  function diff_names(x: i32, y: i32, z: i32): i32
    requires 0 < x < 10;
    requires 10 < y < 20;
    requires 20 < z < 30;
    ensures 80 < return < 140;
    ensures return == x + 2*y + 3*z;

  function diff_names_2(x: i32)
    requires x > 10;
    ensures x > 5;
}

  // Error: interface doesn't require x > 0
  function f1(x: i32)
    requires x > 0;
  {
  }

  // Error: we haven't stated that the implementation ensures return == 100
  function f2(x: i32): i32
  {
    return 100;
  }

  // Error: x > 0 doesn't imply x > 10, and return < 0 doesn't imply return < -10
  function f3(x: i32): i32
    requires x > 10;
    ensures return < 0;
  {
    return -100;
  }

  // Success: return == ~x, together with the interface precondition (x < 0),
  // implies the interface postcondition (return >= 0)
  function f4(x: i32): i32
    ensures return == ~x;
  {
    return ~x;
  }

  // Success
  function f5(x: i32, y: i32)
    requires x >= 0;
    requires y >= 3;
  {
  }

  // Success
  function diff_names(z: i32, y: i32, x: i32): i32
    requires 0 < z < 10;
    requires 10 < y < 20;
    requires 20 < x < 30;
    ensures 80 < return < 140;
    ensures return == 3*x + 2*y + z;
  {
    return z + 2*y + 3*x;
  }

  // Success
  function diff_names_2(a: i32)
    requires a > 10;
    ensures a > 5;
  {}
