module Main
interface {}
  datatype X<a> = X { a, a, i32 };
  datatype Y = Y1 { i32 } | Y2 { i32, i32 };
  datatype Z = Z1 | Z2;

  function f1()
  {
    var a: Y = Y1{100};
    var b: Y = Y2{10,20};
    assert (a == a);
    assert (a != b);
    assert (b == b);
    assert (a == b);    // error
  }

  function f2()
  {
    var a: X<bool> = X<bool> { true, false, 100 };
    assert (a == a);
    assert (a != a);   // error
  }

  function f3()
  {
    assert (Z1 == Z1);
    assert (Z1 != Z2);
    assert (Z1 == Z2);   // fails
  }


  function bad_field()
  {
    var y: Y = Y2 { 100, 0/0 };   // error
    assert (y != y);    // fails -- previous error defining y makes no difference
  }


  function field_values()
  {
    var a: Y = Y2{10,20};
    assert ((match (a) { case Y2(p) => p.0 }) == 10);
    assert ((match (a) { case Y2(p) => p.1 }) == 20);
    assert ((match (a) { case Y2(p) => p.1 }) != 20);   // error
  }

  function field_values_2()
  {
    var b: X<i8> = X<i8> { i8(10), i8(20), 30 };
    match (b) {
      case X(ref p) =>
        assert (p.0 == 10);
        assert (p.1 == 20);
        assert (p.2 == 30);
        assert (p.2 != 30);   // error
    }
  }
