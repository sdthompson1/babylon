module Main
interface {}


  import Foo;

  function test(x: i32)
  {
    // Assert can't be proved because no information about the return value
    // of Foo.f() is available from the interface of Foo.f().
    assert (Foo.f() == 10);      // Error

    // However, if we tell the compiler to consider Foo.g() as well, then
    // the assert can now be proved.
    Foo.g();
    assert (Foo.f() == 10);      // OK


    // Similar case but with an argument.
    assert (Foo.add_one(20) == 21);   // Error
    ghost Foo.add_one_lemma(20);
    assert (Foo.add_one(20) == 21);   // OK
    assert (Foo.add_one(21) == 22);   // Error, as we only applied the lemma for x==20
    
  }


  function test_errors()
  {
    test(1 / 0);  // Error, function argument does not validate
    test(0);      // OK
  }

  function test2()
  {
    // Same as before but using a "proof"
    assert (Foo.f() == 10);  // Error

    assert (Foo.f() == 10)
    {
      Foo.g();
    }
  }
