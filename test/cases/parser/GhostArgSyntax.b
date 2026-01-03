module GhostArgSyntax
interface {
  function f1(ghost x: i32);              // ghost before name
  function f2(x: ghost i32);              // ghost after colon
  function f3(ref ghost x: i32);          // ref ghost
  function f4(ghost ref x: i32);          // ghost ref (order reversed)
  function f5(ref x: ghost i32);          // ref before name, ghost after colon
  function f6(ghost x: ref i32);          // ghost before name, ref after colon
  function f7(x: ref ghost i32);          // both after colon
  function f8(x: ghost ref i32);          // both after colon, reversed
  function f9(x: i32, ghost y: bool);     // mixed ghost and non-ghost
  function f10(ghost x: i32, y: bool, ghost z: u8);  // multiple ghost args

  // Syntax error: duplicate ghost keyword
  function f11(ghost ghost x: i32);
}
