module Imp
interface {
  function foo(x:i32): i32;
  ghost function foo_lemma(x:i32)
    ensures foo(x) == 99;

  function bar(x:i32, y:i32): bool;
  ghost function bar_lemma(x:i32, y:i32)
    ensures bar(x,y) == (x < y);
}


  function foo(x:i32): i32
  {
    return 99;
  }

  ghost function foo_lemma(x:i32)
    ensures foo(x) == 99;
  {
  }

  function bar(x:i32, y:i32): bool
  {
    return x < y;
  }

  ghost function bar_lemma(x:i32, y:i32)
    ensures bar(x,y) == (x < y);
  {
  }
