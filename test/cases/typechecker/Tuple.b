module Tuple
interface {}
  datatype D<a> = D;

  function f1(x: {D,D})
  {
  }

  function f2(x: {i32,i8})
  {
  }

  function f3()
  {
    var x: {i32,i16};
    f2(x);
  }

  function f4(x: {i32, i32})
  {
    var a: i32 = x.0;   // ok
    var b: bool = x.1;  // type mismatch
    var c = x<>.2;      // no such field  (empty <> are ignored)
  }

  function f5(): D
  {
  }
