module Statements
interface {}
  function unexpected_return()
  {
    return 10;
  }

  function return_wrong_type(): i32
  {
    return true;
  }

  function return_without_value(): i32
  {
    return;
  }

  function var_wrong_type()
  {
    var x: bool = 100;
  }

  function assign_wrong_type()
  {
    var x: i32;
    x = true;
  }

  function var_wrong_type_rhs()
  {
    var x: i32 = true;
  }

  function invalid_var()
  {
    var x;      // error, incomplete definition of x
    x = true;   // should not generate a further error
  }

  function assign_not_lvalue()
  {
    var x: i32;
    x + 1 = 2;
  }

  function param_wrong_type(x: i32, y: i32)
  {
    var z: bool = x;
  }

  function var_type_inference(): bool
  {
    var b = true;
    return b;
  }

  function bad_rhs(): i32
  {
    var x: i32 = 2 + true;
    x = 1 + true;
    return 3 + false;
  }

  const func_const = var_type_inference;

  function func_var()
  {
    var x = var_type_inference;
  }

  function func_let(): i32
  {
    return (let f = var_type_inference in 1);
  }



  ghost function test_ghost_func(): i32
  {
    return 100;
  }

  function test_exec_func(): i32
  {
    return 100;
  }

  function exec_cant_call_ghost(): i32
  {
    return test_ghost_func();   // Error
  }

  ghost function ghost_can_call_exec(): i32
  {
    return test_exec_func();  // OK, returns 100
  }



  const test_const: i32 = 100;
  
  function cant_assign_to_consts()
  {
    test_const = 99;
    test_exec_func = 100;
  }



  function assert_stmts()
  {
    assert (1 == 2);      // OK
    assert (1);           // Error, not boolean
    assert (1 + true);    // Error, assert expr doesn't typecheck
  }


  function while_stmts()
  {
    while (99)           // Wrong type, must be bool
      invariant 75;     // Wrong type, must be bool
      decreases 0;
    {
    }

    while (true)
      decreases 1 + true;   // Decreases doesn't typecheck
    {
      var x: i32 = true;    // Body doesn't typecheck
    }

    while (true)
      decreases cant_assign_to_consts;    // Can't use function type here
    {
    }

    while (true)
      decreases {x=1};        // Can't use record as decreases
    {
    }

    while (true)
      decreases {1,{2,3}};    // Tuple is ok (even nested)
    {
    }

    while (true)
      decreases {1,{true,{x=1}}};   // error: non-decreasable type embedded within tuple
    {
    }

    while (true)
      decreases {};       // empty tuple is accepted
    {
    }
  }


  function f1(x: i32): i32
  {
    return 1;
  }
  
  function f2(x: i32)
  {
  }

  function call_stmts()
  {
    f1(100);    // Error, return value being ignored
    f2(100);    // OK
    f2(true);   // Error, argument has wrong type
  }


  datatype T = A | B{i32,bool};

  function match_stmt(): i32
  {
    match (1) {     // Error, no arms
    }

    // Successful match, w/ multiple statements per case
    var x: i32 = 0;
    var y: i32 = 1;
    match (A) {
      case A =>
        x = 1;
        y = 2;
        x = x + y;
      case _ =>
        x = 2;
        y = 3;
    }

    match (A) {
      case A => return 1;   // OK
      case B{i,b} => return b;  // Error
      case B{i,b} => return i;  // OK
      case 123 => return 0;    // Error
    }
  }
