module Foo

interface {
    // T is declared allocated, so (from the interface's point of view)
    // D is also allocated.
    type T (allocated);
    datatype D = MkD(T);
}

// Inside Foo, D is not really allocated (see AllocRecompute.b), but
// importers can only see that T might be allocated.
type T = i32;
