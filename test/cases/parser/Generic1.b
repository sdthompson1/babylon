module Generic1
interface {
  function f<a>();

  function test()
  {
    f<i32>;
  }
}
