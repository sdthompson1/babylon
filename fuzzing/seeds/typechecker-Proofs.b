module Main
interface {}


  ghost function cant_write_to_fix()
  {
    assert forall (k:i32) k == 99
    {
      fix k: i32;
      k = 99;      // Error, "fix" variables are considered read-only
    }
  }

  ghost function cant_fix_outside_proof()
  {
    fix x: i32;    // Error, "fix" can only be used inside a proof of an assert
  }

  ghost function fix_no_forall()
  {
    assert (1 == 1)
    {
      fix x: i32;    // Error, "fix" can only be used when we are proving a forall-statement
    }
  }

  ghost function fix_wrong_type()
  {
    assert (forall (x:i32) forall (y:i16) true)
    {
      fix xx: i32;    // OK
      fix yy: i32;    // Error, wrong type, must be i16
    }
  }

  ghost function fix_wrong_scope()
  {
    assert (forall (x:i32) forall (y:i32) true)
    {
      fix a:i32;
      if (a > 0) {
        fix b:i32;    // Error, fix must be in the outermost scope
      }
    }
  }


  ghost function obtain_non_bool()
  {
    obtain (x:i32) 1+2;     // Type error (expected bool)
  }

  ghost function obtain_ok()
  {
    obtain (x:i32) x > 0;
    x = 99;   // Overwriting an "obtain" variable is allowed (for now)
  }

  function obtain_exec()
  {
    obtain (x: i32) x == 1;   // OK, but x is a ghost
    x = 2;    // Error, writing to ghost variable (from non-ghost code)
  }


  ghost function cant_use_outside_proof()
  {
    use 1;   // error
  }

  ghost function use_no_exists()
  {
    assert (1 == 1) {
      use 2;    // error
    }
  }

  ghost function use_wrong_type()
  {
    assert (exists (x: i32) x == 10) {
      use true;   // error, wrong type
    }
  }

  ghost function use_wrong_scope()
  {
    assert (exists (x: i32) true) {
      if (1 == 2) {
        use 3;   // error, use must be in the outermost scope
      }
    }
  }
