module Main
interface {}

import Import;

// This will error, because even though c is defined to be 100, this fact
// is not exported as part of the interface of Import, so technically
// the value of Import.c is "not known at compile time" at this point.
const foo: i32 = Import.c;
