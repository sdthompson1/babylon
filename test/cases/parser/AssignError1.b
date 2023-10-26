module Main
interface {
  function f(): i32
  {
    *      // This will try to parse "*" as an assignment lhs, and fail
  }
}