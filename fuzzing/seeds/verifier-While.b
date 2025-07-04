module While
interface {}
  function f1()
  {
    var x: i32 = 100;
    while (x > 0)
      invariant 0 <= x < 100;    // Not satisfied on entry to loop
      decreases x;
    {
      x = x - 1;
    }
  }

  function f2()
  {
    var x: i32 = 100;
    while (x > 0)
      invariant x == 100;      // Not satisfied on exit from loop
      decreases x;
    {
      x = x - 1;
    }
  }


  function f3()
  {
    var x: i32 = 100;
    while (true)
      decreases x;            // Doesn't decrease       
    {
      x = 99;
    }
  }


  function f4()
  {
    while (true)
      invariant 1/0 == 0;     // Invariant is nonsense
      decreases 0;
    {
    }
  }


  function f5()
  {
    while (true)
      decreases 1/0;          // Variant is nonsense
    {
    }
  }


  function f6()
  {
    var x: i32 = 100;
    while (true)
      invariant 200/x == 2;   // Valid on 1st iteration, but not 2nd+ because x might be zero
      decreases x;
    {
      x = x - 1;
    }
  }


  function f7()
  {
    var x: i32 = 100;
    while (100/x == 1)     // Valid on 1st iteration but not 2nd+
      decreases x;
    {
      x = x - 1;
    }
  }


  function f8()
  {
    var x: i32 = 100;
    while (x > 0)
      decreases 100/x;   // Valid on 1st iteration but not 2nd+
    {
      x = 0;
    }
  }


  function f9()
  {
    var b: bool = true;
    while (b)
      decreases b;   // Boolean loop variant (false is considered lower than true)
    {
      b = false;
    }
  }


  function f10()
  {
    while (true)
      decreases 0;
    {
      var x: i32 = 0 / 0;       // Invalid loop body
    }
  }


  function f11()
  {
    var x: i32 = 10;
    var y: i32 = 0;
    while (x > 0)
      decreases x;
      invariant 0 <= x <= 10;
      invariant y <= 10*(10-x);
    {
      // If within while
      if (x == 5) {
      
        // Var decl within while
        var z: i32 = 10;
        y = y + z;
      } else {

        // Nested while within while  
        var z: i32 = 4;
        while (z > 0)
          decreases z;
          invariant 0 <= z <= 4;
          invariant y <= 10*(10-x) + (4-z);
        {
          y = y + 1;
          z = z - 1;
        }
      }

      x = x - 1;
    }
  }


  function f12(): i32
  {
    var x: i32 = 10;
    while (x > 0)
      invariant x == 10;
      decreases x;
    {
      x = 20;
      return x;

      // The invariant is false here, but the code never reaches
      // this point so it doesn't matter
    }

    // False is now provable, because the invariant implies x == 10, but
    // the negated loop-condition implies x <= 0, which is contradictory.
    assert (false);
  }


  function f13()
  {
    var x = {1,2,3};
    while (x.2 > 0)
      invariant x.2 >= 0;
      decreases x.2;
    {
      x.2 = x.2 - 1;
    }

    assert (x.2 == 0);
    assert (x.2 != 0);   // fails
  }

  function f14()
  {
    var x = 3;
    ref r = x;
    while (x > 0)
      decreases x;
      invariant x >= 0;
    {
      assert (x == 3);   // Should fail
      r = r - 1;
    }
  }


  // tuple for decreases
  function f15()
  {
    var x = 10;
    var y = 8;
    while (y > 0)
      invariant x > 0;
      invariant y >= 0;
      decreases {y,x};
    {
      x = x - 1;
      if (x == 0) {
        x = 10;
        y = y - 1;
      }
    }
  }


  // empty tuple - accepted, but does not decrease
  function f16()
  {
    while (true)
      decreases {};   // Error, does not decrease
    {
    }
  }

  function f17()
  {
    while (false)
      decreases {};   // OK because loop doesn't execute
    {
    }
  }


  function f18()
  {
    // Variable modified through reference
    var i = 10;
    var x = 20;
    
    while (i > 0)
        decreases i;
        invariant 0 <= i <= 10;
        invariant x == 20 + (10 - i);
    {
        i = i - 1;

        ref r = x;
        r = r + 1;
    }

    assert (x == 30);   // OK
    assert (0 == 1);    // Should fail (previously was accepted due to a bug, modification to x via r was missed.)
  }


// Regression tests - Variable modified by passing as a ref-arg
function subtract_one(ref x: i32)
    requires x > 0;
{
    x = x - 1;
}

function f19()
{
    var x = 100;
    
    while x > 0
        decreases x;
    {
        subtract_one(x);
        assert x == 99;   // Fails (but only if the compiler notices that x is modified in the loop)
    }
}

function subtract_two(ref x: i32): bool
    requires x > 0;
{
    x = x - 2;
    return true;
}

function f20()
{
    var x = 100;
    while x > 0
        decreases x;
    {
        var b = subtract_two(x);
        assert x == 98;   // Should fail
    }
}

function f21()
{
    var x = 100;
    while x > 0
        decreases x;
    {
        var b = false;
        b = subtract_two(x);
        assert x == 98;   // Should fail
    }
}

function f22()
{
    var x = 100;
    while x > 0
        decreases x;
    {
        var b = false;
        ref r = x;
        b = subtract_two(r);
        assert x == 98;   // Should fail (x modified via r)
    }
}

function f23()
{
    // Missing "decreases". (This is now a verifier error, not a typechecking error.)
    while (true) { }
}
