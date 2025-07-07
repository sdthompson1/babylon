module DoubleImport

interface {}

import Test;
import Test as T;

const x: i32 = I32_MIN;  // Should be valid - double import does not cause ambiguity.

const y: i32 = Test.I32_MIN;  // Valid
const z: i32 = T.I32_MIN;     // Also valid

const w: i32 = M.I32_MIN;     // Invalid: M is not an imported module.
