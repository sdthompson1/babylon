module Ghost
interface {}

ghost function byref(ref x: i32)
{}

// Executable function
function f()
{
    var v: i32       = 50;
    ghost var g: i32 = 100;

    g = 200;          // Error, writing to ghost from executable code
    ghost g = 200;    // OK

    v = 250;          // OK
    ghost v = 250;    // Error, writing to real variable from ghost code

    assert (1 == 1)
    {
      var b: bool = forall (x:i32) x != x;      // OK, proofs are ghost code, so b is a ghost var
      return;         // Error, can't return from ghost code
    }

    assert (forall (x:i32) x == x);     // OK, assert rhs is always nonexecutable

    ghost if (true) {
      g = 999;    // OK
      v = 999;    // Error, inside ghost if block, so can't write to v
    }

    while (v > 0)
      decreases v;
      invariant forall (x:i32) x == x;    // OK, invariants are nonexecutable
    {
      v = v - 1;
    }

    ghost byref(g);  // OK, writing to ghost variable
    ghost byref(v);  // Error, trying to write to nonghost variable from ghost stmt.
}


// Uninterpreted ghost function, with preconditions - allowed
ghost function uninterp_1(x: i32): i32
    requires x > 10;

// Uninterpreted ghost function, with postcondition - not allowed
ghost function uninterp_2(): i32
    ensures return > 10;
