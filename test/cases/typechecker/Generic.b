module Generic
interface {
  function id<a>(x: a): a;

  function test2()
  {
    var x: i32 = id(100);                // OK, id<i32> is inferred
    var y0: i32 = id<>(100);             // Error, not enough type parameters
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

  function test5()
  {
    var v1 = {1,2};
    var v2 = v1.0<i32>;     // Illegal use of type parameter
    var v3 = id<i32>;       // Can't use function as value
  }
}
