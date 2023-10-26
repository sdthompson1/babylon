module Ref5
interface {
  function f(): i32
    ensures old(return) == 10;
  {
  }
}
