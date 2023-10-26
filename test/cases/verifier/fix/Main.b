module Main
interface {

  function main();

}

  import Imp;

  ghost function test_asserts()
  {
    assert (forall (x:i32) Imp.foo(x) == 99)
    {
      fix i:i32;
      Imp.foo_lemma(i);
    }

    assert (forall (x:i32) forall (y:i32) Imp.bar(x,y) ==> x < y)
    {
      fix a:i32;
      fix b:i32;
      Imp.bar_lemma(a, b);
    }
  }

  function main()
  {
  }
  