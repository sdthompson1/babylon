module Foo
interface {
  function f(): i32;

  function g()
    ensures f() == 10;

  function add_one(x: i32): i32
    requires x < 100;

  ghost function add_one_lemma(x: i32)
    requires x < 100;
    ensures add_one(x) == x + 1;
}

  function f(): i32
  {
    return 10;
  }

  function g()
    ensures f() == 10;
  {
  }

  function add_one(x: i32): i32
    requires x < 100;
  {
    return x + 1;
  }

  ghost function add_one_lemma(x: i32)
    requires x < 100;
    ensures add_one(x) == x + 1;
  {
  }
