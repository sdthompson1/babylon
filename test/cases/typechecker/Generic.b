module Generic
interface {
  function id<a>(x: a): a;

  function test2()
  {
    var x: i32 = id(100);                // Error, missing type parameter
    var y: i32 = id<i32, i32>(100);      // Error, too many type parameters
    var w: bool = id<i32>(100);    // Error, rhs has type i32, doesn't match bool
  }


  function test3<a>(x: i32): i32    // Redundant type parameter, but that's OK
  {
  }


  function test4<a,b>(x: a, y: b)
  {
    var v1: a = id<a>(y);     // Error, y has type b, doesn't match a
    var v2: b = id<a>(x);     // Error, rhs has type a, doesn't match b
    var v3: a<i32>;           // Error, wrong number of tyargs
  }
}
