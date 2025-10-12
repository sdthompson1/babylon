module Main
interface {
  function foo<a>(x: a, y: b)
  {
    var v: b2 = b3(x);
    assert (forall (z: b4) true);

    fix f: b5;
    obtain (o: b6) true;

  }

  const c: i32 = foo<badtype>(1, 2);
  const c2: badtype2;

  function bar<a>(x: i32): i32
  {
    assert (forall (i: x) true);    // x not in scope
    var v: i32;
    obtain (o: v) true;         // v not in scope
    return a;                   // a not in scope
  }
}
