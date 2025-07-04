module PrePost
interface {}

  // Postconditions:
  
  function ret_postcond_error(x: i32): i32
    ensures return == 99;    // not satisfied
  {
    return 25;    // error reported here
  }

  function no_ret_postcond_error()
    ensures 1 == 2;
  {
    var x: i32 = 99;
  }   // error reported here

  function invalid_postcond()
    ensures 1/0 == 1;      // Error reported here (1/0 is not allowed)
  {
  }    // Also here, because we cannot know if 1/0 == 1

  function reach_end_of_func(): i32
  {
  }    // Error reported here


  // Preconditions:

  function add_one(x: i32): i32
    requires 0 < x < 100;
    requires 0/x == 0;
    ensures return == x + 1;
    ensures 0/return == 0;
    ensures return > x;
  {
    var y: i32 = x + 1;
    return y;
  }

  function test_add_one(): i32
    ensures return == 98;
  {
    var z: i32 = add_one(200);   // Precondition error
    return add_one(97);
  }


  // Asserts:
  function assert_test(x: i32)
    requires x < 100;
  {
    assert (x < 200);    // succeeds (using precondition)
    assert (x < 50);     // fails (assert not true)
    assert (1/0 == 1);   // fails (assert term doesn't verify; then the assert itself fails)
  }


  // Regression test: Verify that we are only asserting postconditions
  // under the assumption that the preconditions are true. Otherwise
  // 1==0 can be proved in the following example.
  function foo(x: i32): i32
      requires x > 10;
      ensures x < 10 ==> false;
  {
      return 20;
  }
  function foo_test()
  {
      assert foo(11) == 20;  // OK
      assert 0 == 1;         // Error
  }
