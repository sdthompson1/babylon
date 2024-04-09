module Functions
interface {}
  function foo(): i32
  {
    var x: i32 = 1;
    var y: i32 = 2;
    
    var a: i32 = x / (y - 2);     // Vardecl rhs fails to verify
    var b: i32;
    b = x / 0;                    // Assignment rhs fails to verify

    return 0 / 0;                 // Return expr fails to verify
  }


  function err_after_return_ignored(): i32
  {
    return 10;
    var x: i32 = 1/0;
  }

  function with_args(b: bool, x: i32, y: i32): i32
  {
    var c: i32 = (if b then x else y);
    return c;
  }

  function void_ret()
  {
    return;
  }


  function call()
  {
    var x: i32 = with_args(true, 1, 2);
    var y: i32 = with_args(false, 1, 2);
    var z: i32 = x + y;    // Should verify because x==1, y==2
  }

  function bad_call(x: i32): i32
  {
    return with_args(true, 2*x, x);
  }


  function assignment(x: u8): u8
  {
    var y: u8 = x;
    y = ~y;
    return y;
  }

  function call_assignment(): u8
  {
    var err: u8 = assignment(1) + 2;     // Busts u8 maximum
    return assignment(1) + 1;     // Is fine
  }


  function var_fails_to_verify()
  {
    var x: i32 = 1/0;      // Error (Line 63)
    var y: i32 = x + 1;    // Error, can't know what "x" is therefore might not be able to add 1 to it

    var z: i32 = 0;
    z = 1/0;               // Error (Line 67)
    var w: i32 = z + 1;    // Error
  }
