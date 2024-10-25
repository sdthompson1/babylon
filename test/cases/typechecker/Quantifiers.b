module Quantifiers
interface {}

  function fn1()
  {
    assert (forall (x:i32) x == x);    // Valid
    assert (forall (x:i32) x + 1);     // Type error, not boolean
    assert (exists (x:i32) x + true);  // Type error, body doesn't typecheck
  }

  function fn2(): bool
    requires forall (x:i32) x == x;         // Valid, preconds don't count as executable
  {
    var b: bool = forall (x:i32) x != x;    // Error, can't use quantifier in executable code
    assert (b == false);                      // Valid, asserts don't count as executable
    return exists (x:i32) x == 1;           // Error, can't use quantifier in executable code
  }

  ghost function fn3(): bool
  {
    return forall (x:i32) x != x;           // Valid, ghost function so can use quantifiers
  }


  const c1: bool = true;
  const c2: bool = exists (x:i32) x == 42;   // Error, const is considered executable code
