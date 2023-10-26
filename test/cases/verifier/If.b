module If
interface {}

  function f1(x: i32)
  {
    var y: i32 = 200;

    if (x == 0) {
      y = 100;
    }

    assert (x == 0 ==> y == 100);
    assert (x != 0 ==> y == 200);
  }

  function f2(x: i32)
  {
    var y: i32;

    if (x == 0) {
      y = 100;
    } else {
      y = 200;
    }

    assert (x == 0 ==> y == 100);
    assert (x != 0 ==> y == 200);

    assert (x != 0 ==> y != 200);   // Fails
  }
