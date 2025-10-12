module Main
interface {}
  function f1(ref x: i32, ref y: i32)
    requires 0 < x < 1000;
    requires 0 < y < 1000;
    ensures x == old(x) + old(y);
    ensures y == old(x) - old(y);
  {
    var tmp = y;
    y = x - y;
    x = x + tmp;
  }

  function f2()
  {
    var xx = 1;
    var yy = 2;
    f1(xx, yy);
    assert (xx == 3);     // OK
    assert (yy == -1);    // OK
    assert (yy != -1);    // Error
  }

  function f3(ref x: i32)
    requires 0 <= x <= 1000;

    // because postconditions are checked before examining the body
    // of the function, this is needed:
    ensures 0 <= x <= 1000;

    // here "old(x)" means input value of x, "x" means output
    ensures old(x) + x == 1000;

    // here y captures the new value of x, so
    // "old(y)" and "y" both refer to the output value of x.
    ensures let y = x in old(y) + y == 2000 - 2*old(x);

    // here y captures the old value of x.
    ensures let y = old(x) in old(y) + y == 2*old(x);

    // negative case.
    ensures let y = x in old(y) + y == 0;
  {
    x = 1000 - x;
  }

  // ref args w/o validity conditions
  // (this is to cover a "return NULL" case in the code!)
  function f4(ref x: bool): bool
  {
      return true;
  }

  function f4_test()
  {
      var x = true;
      var v = f4(x);
      assert v;
  }
