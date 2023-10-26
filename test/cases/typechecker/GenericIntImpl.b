module GenericIntImpl

// Checking that generic implementations match the interface.

interface {
  function f1<a>(x: a): i32;

  function f2<a,b>(x: a, y: b): i32;

  function f3<a,b,c>(x: i32): i32;
}

  // Currently we require an exact match (no alpha conversion allowed)
  // so the following fails, because "a" does not match "b".
  function f1<b>(x: b): i32     // Error
  {
    return 42;
  }


  // The following fails because the types genuinely don't match
  function f2<a,b>(x: b, y: a): i32
  {
    return 42;
  }


  // The following fails because there are different numbers of tyvars.
  function f3<a>(x: i32): i32
  {
    return 42;
  }
