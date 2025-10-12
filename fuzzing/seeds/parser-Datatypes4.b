module Main
interface {}
  datatype D = D { i32, i32 };

  function f()
  {
    var v: D = D { 100, ^ };
  }
