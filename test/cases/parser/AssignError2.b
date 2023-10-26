module AssignError2
interface {
  function f(): i32
  {
    x 1      // Expected "=" between "x" and "1"
  }
}
