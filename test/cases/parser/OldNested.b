module OldNested
interface {
  function f(x: i32): i32
    ensures old(old(x) + return) == 10;
  {
  }
}
