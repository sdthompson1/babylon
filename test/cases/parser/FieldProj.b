module FieldProj
interface {
  const x: i32 = a.b;       // Valid
  const y: i32 = a.0;       // Valid
  const z: i32 = a.(1+2);   // Invalid
  const a = a._;            // Invalid
  const b = a.0a;           // Invalid
}
