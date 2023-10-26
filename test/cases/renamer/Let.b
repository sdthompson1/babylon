module Let
interface {
  // Let isn't recursive
  const a: i32 = let z = z in 100;        // Line 4
}
