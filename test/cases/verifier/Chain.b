module Chain
interface {}
  const x: i32 = if 1 < 2 <= 3 then 1/0 else 0;  // Error
  const y: i32 = if 1 < 2 <= 1 then 1/0 else 0;  // OK
  const z: i32 = if false ==> false ==> false then 0 else 1/0;   // OK
