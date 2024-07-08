module IllegalReturn
interface {
  function foo()
    ensures return == 1;
  {
  }

  function bar()
  {
    var x: i32 = return;
  }
}
