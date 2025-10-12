module Main
interface {
  function f<a>();

  function test()
  {
    f<i32>;
  }
}
