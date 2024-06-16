module ArrayLit

interface {}

const a1: i32[] = [true, false];   // Wrong type

const a2 = [1, true];       // Types do not agree

const a3 = [];              // Empty array literal (now works - the compiler picks a "default" type)

const a4 = [0, 1 + true];   // Type error in one of the elements


function foo(): i32 { return 0; }

const a5: i32[3] = [1, 2, foo()];  // Non compile time constant


// Compile time evaluation of e1[e2]

const i1: i32 = [1, 2, 3][99];   // Array index out of bounds

const i2: i32 = [foo()][0];        // LHS not a compile time constant

const i3: i32 = [1, 2, 3][foo()];  // RHS not a compile time constant

const arr: i32[] = [1, 2, 3];
const i4: i32 = arr[99];         // Index out of bounds. LHS includes a cast.
