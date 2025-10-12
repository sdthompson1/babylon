module Main
interface {
  const x: i32 = a.b;       // Valid
  const y: i32 = a.0;       // Valid
  const z: i32 = a.(1+2);   // Invalid
}