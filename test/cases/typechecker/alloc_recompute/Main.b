module Main

interface {
    // Same shape as in Foo, but here T2 really is allocated.
    type T2 (allocated);
    datatype D2 = MkD2(T2);
    type U2;

    // Realized (below) by Foo's D.
    type V;
}

import Foo;

type T2 = i32[*];  // Allowed: T2 was declared allocated, and i32[*] is acceptable for an (allocated) type.

type U2 = D2;  // Should fail, U2 was declared non-allocated, but D2 is allocated (because T2 is).

// Should fail. Foo's implementation knows that T = i32, so D is not
// allocated there, but this module can only see Foo's interface, which
// says that T (and hence D) might be allocated.
type V = D;
