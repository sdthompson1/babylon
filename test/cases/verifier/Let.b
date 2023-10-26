module Let
interface {}
  // Verifier can see the value of "let" variables
  const a: i32 = let z = 0 in 1/z;

  // Verifier can understand a "let" expression
  const b: i32 = 1 / (let z = 1 in z-1);
