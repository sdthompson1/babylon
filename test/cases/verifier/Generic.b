module Generic
interface {}
  function id<a: Copy>(x: a): a

  {
    return x;
  }

  function fst<a: Copy, b: Copy> (x: a, y: b): a

  {
    return x;
  }

  function test_id()
  {
    assert (id<i8>(10) == 10);     // Success
    assert (id<i32>(100) == 99);   // Error, returns 100 not 99
  }

  function test_fst()
  {
    assert (fst<bool, i32>(true, 100));         // Success
    assert (fst<i32, bool>(99, false) == 100);  // Failure, returns 99
  }

  function calls_id<T: Copy>(x: T): T

  {
    var T: T = x;      // This is fine, variable "T" is distinct from type "T"
    return id<T>(T);   // Fine, this is basically id(x) which is x
  }

  function test_calls_id()
  {
    assert (calls_id<i32>(12345) == 12345);
  }


  function tru<a>(x: a): bool
  {
    return true;
  }

  function pre_post_cond<a>(x: a, y: bool)
    requires forall (z: a) tru<a>(z) && tru<a>(x) && y;
    ensures forall (z: a) tru<a>(z);
  {
  }

  function test_precond()
  {
    pre_post_cond<i32>(10000, true);
    assert (true);
    pre_post_cond<i32>(9000, false);   // Error, precondition violated
  }
