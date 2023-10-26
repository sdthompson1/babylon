module Let
interface {
  // RHS of let doesn't typecheck
  const a: i32 = let z = 1 + true in z;   // Line 4

  // Body of let doesn't typecheck
  const b: i32 = let z = 1 in z + true;   // Line 7
}
