module DeclsBad
interface {
  const x: i32 = true;    // Const doesn't match claimed type
  const r: i32 = r + 1;   // Illegal recursion
  const a;                // Incomplete definition (type not stated in the interface)
  const b;                // Incomplete definition (type not stated in interface, and no implementation)
  const c: i32;           // Valid here, but the implementation is wrong (see below)

  function f(): i32;      // Incomplete definition
}

  const a: i32 = 100;
  const c: i32;           // Incomplete definition (no right-hand-side in implementation)  
  const d: i32;           // Same (but without a corresponding interface this time)

  function f(): i32;      // Incomplete definition
  function g(): i32;      // Incomplete definition w/o corresponding interface

  function rec_attr(): bool
    requires rec_attr();  // Illegal, cannot use function in its own attributes (currently)
    ensures rec_attr();   // Ditto
  {
    return true;
  }

  function assign_to_param(x: i32)
  {
    x = 1;   // This is not allowed, args are considered const.
  }
