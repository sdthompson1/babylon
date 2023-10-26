module DeclsGood
interface {
  const x = 100;     // Const with no type (it should be inferred)
  const a: i32;      // Const without right-hand-side. Accepted because an implementation is provided.

  function foo(x: i32): i32;

  function main();
}

  import Test;

  const a: i32 = 42;

  function foo(arg: i32): i32
  {
    return arg;
  }

  function main()
  {
    Test.print_i32(x);
    Test.print_i32(a);
  }
  