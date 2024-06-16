module Calls
interface {}
  function foo(): i32
  {
    return 1;
  }

  function bar(x: i32, y: i32): i32
  {
    return 2;
  }

  function call(): i32
  {
    var x      = foo();
    var y: i32 = bar(x, 99);
    return x + y;
  }

  function noret()
  {
  }

  function bad_calls()
  {
    var x: i32 = 1;

    var a: i32 = x();    // Not a function

    var b: i32 = foo(1,2,3);   // Too many arguments
    var c: i32 = bar(2);       // Not enough arguments

    var d: i32 = bar(true, false);   // Type mismatch in argument
    var d2: i32 = bar(foo, 3);       // Trying to pass function as argument

    var e: bool = bar(1,2);          // Type mismatch in result

    var f = noret();          // Function doesn't return a value

    var g = (if true then foo else foo)();    // Function not allowed in an if-expr
    var h = (let x = 1 in foo)();             // Function must be a simple variable (Not the best error message here, but it will do for now)

    var i = bar(false, true, true);   // Wrong number of args. (No type errors reported for the args themselves, because the number of args is wrong.)
  }
