module InterfaceWithoutImpl
interface {
  const x: i32;
  const y: i32;

  function foo(x: i32): i32;
  function bar(x: i32): i32;
}

  const x: i32 = 100;

  function foo(x:i32): i32
  {
    return x;
  }
