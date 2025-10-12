module Main
interface {}
  datatype D = A(i32);

  function f1()
  {
    assert ((match (A(100)) { case A(p) => p+1 }) == 101);  // OK
    assert ((match (A(100)) { case A(p) => p+1 }) == 102);  // Fails
  }

  function f2()
  {
    var d: D = A(100);
    match (d) {
      case A(ref p) =>
        p = p + 1;    // Update d's payload via the reference, it should now be 101 instead of 100.
    };   // redundant semicolon...
    assert (match (d) { case A(x) => x == 101 });  // OK
    assert (match (d) { case A(x) => x == 102 });  // Fails
  }
