module Chain
interface {}

function f()
{
  var x: i32 = if 1 < 2 <= 3 then 1/0 else 0;  // Error
  var y: i32 = if 1 < 2 <= 1 then 1/0 else 0;  // OK
  var z: i32 = if false ==> false ==> false then 0 else 1/0;   // OK
}
