module OldRequires
interface {
  function f(x: i32)
    requires old(x) > 0;
  {
  }
}
