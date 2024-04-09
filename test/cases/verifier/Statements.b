module Statements
interface {}
  function simple_if()
  {
    var x: i32 = 100;

    if (x + 1 == 101) {
      assert (true);
      x = x + 3;
    } else {
      assert (false);
    }

    assert (x == 103);   // Succeeds
    assert (x == 104);   // Fails
  }
  

  function control_reaches_end(x: i32): i32
  {
    if (x == 0) {
      return 24;
    }
  }    // Error, control reaches end of function

  function control_doesnt_reach_end(x: i32): i32
  {
    if (x == 0) {
      return 20;
    }
    if (x != 0) {
      return 30;
    }
  }    // OK, all cases are covered by the ifs


  function complex_variable_assignments(x: i32, y: i32)
  {
    var z: i32;
    if (x == 1) {
      z = 20;
      if (y == 2) {
        var z: i32;
        z = 999;
      } else {
        z = 30;
      }
    } else {
      if (x == 2) {
        z = 25;
      } else {
        z = 35;
      }
    }
    assert (z == 20 || z == 30 || z == 25 || z == 35);   // Succeeds
    assert (z == 0);   // Fails
  }


  function return_in_else(x: i32)
  {
    var y: i32 = 99;
    if (x == 0) {
      y = 100;
    } else {
      return;
    }
    assert (y == 100);
  }

  function return_in_both_branches(x: i32)
  {
    var y: i32 = 99;
    if (x == 0) {
      y = 100;
      return;
    } else {
      y = 101;
      return;
    }
    y = 102;
    assert (y != 102);  // Passes because we can't reach here
    assert (y == 102);  // Passes because we can't reach here
  }

  function verif_fail_one_branch(a: bool)
  {
    var x: i32 = 100;
    if (a) {
      x = 1/0;       // Error
    } else {
      x = 99;
    }
    assert (x == 98);  // Error, assert might not be true
  }

  function verif_fail_if_condition()
  {
    var x: i32 = 0;
    if (1/0 == 1) {   // Error
      x = 1;
      assert (false);     // Fails
    } else {
      x = 2;
    }
    assert (x == 0);      // Fails
  }

  function path_conds(x: i32)
  {
    var y: i32;
    if (x != 0) {
      y = 100 / x;     // Succeeds because of path condition (x!=0 assumed on "then" branch)
    } else {
      assert (x == 0);   // Succeeds because of path condition (!(x!=0) assumed on "else" branch)
    }
  }

  function default_init_1(x: i32)
  {
    var z: i32;
    assert (z == 0);
    var b: bool;
    assert (b == false);
  }

  function default_init_2(x: i32)
  {
    var z: i32;
    if (x > 1) {
      z = 1;
    }
    assert (z == 0 || z == 1);
  }
