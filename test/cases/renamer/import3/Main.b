module Main

interface {}

import A;
import B;
import qualified Q;

const c1 = same_name;    // Ambiguous, could be A.same_name or B.same_name (but not Q.same_name)
const c2 = A.same_name;  // OK
const c3 = Q.same_name;  // OK
const c4 = q;            // Not in scope (must refer to as Q.q)
const c5 = Q.q;          // OK

