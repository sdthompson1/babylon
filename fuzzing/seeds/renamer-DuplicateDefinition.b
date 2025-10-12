module Main
interface {
  const cx: i32 = 1;
  const cx: i32 = 1;

  function duplicate_arg(ax: i32, ax: bool);
}

const cy: i32 = 1;
const cy: i32 = 1;

function duplicate_variable()
{
  var vx: i32 = 1;
  var vx: i32 = 2;
}

function duplicate_arg_var(x: i32)
{
  var x: i32 = 200;
}

function duplicate_fix(x: i32)
{
  assert (forall (a:i32) forall (b:i32) true)
  {
    fix f: i32;
    fix f: i32;   // Duplicate
  }
}
