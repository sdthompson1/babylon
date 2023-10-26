module Main

interface { function main(); }

// A case where we have ambiguity between an imported module, and a
// local object.

import qualified Foo as F;    // exports x and z
import Test;

const F = {x=1, y=2};

const test1 = F.x;    // Ambiguous, Foo.x or Main.F.x

const test2 = F.y;    // OK, Main.F.y, because there is no Foo.y

const test3 = F.z;    // Ambiguous, Foo.z or Main.F.z
                      // (the fact that Main.F doesn't have a z field is irrelevant
                      // because the renamer doesn't look at the types).
                      
const test4 = F.bad;  // OK, Main.F.bad
                      // (again, the fact that 'bad' is missing from Main.f
                      // doesn't matter)
