module ArgError
interface {
  function f(100): i32     // Error, expecting argument name
  {}
}