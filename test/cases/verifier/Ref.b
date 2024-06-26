module Ref
interface {}
  function f1()
  {
    var v = {{1,2,3},4,5};
    ref r = v.0.1;
    r = 1000;
    assert (v == {{1,1000,3},4,5});    // OK
    assert (v != {{1,1000,3},4,5});    // Fails
  }

  function f2()
  {
    var v = {1,2};
    ref r1 = v.1;
    ref r2 = r1;

    r2 = 1/0;     // Error, divide by zero

    assert (v.1 == 99);    // Error, 1/0 is indeterminate, might not be equal to 99.
  }

  function f3()
  {
    var v = {{1,2},3};
    ref r1 = v.0;
    
    r1.0 = 1/0;   // Error, divide by zero

    assert (v.0.0 == 99);   // Error, 1/0 is indeterminate
  }

  function f4(x: i32[10])
  {
    ref v = x[20];  // Error, array index might be out of range
  }
