module Main
interface {
  function f(): i32
    ensures old(return) == 10;
  {
  }
}
