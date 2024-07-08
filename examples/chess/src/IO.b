// IO is used as a "tag" to indicate that an external C function
// does I/O or otherwise is not a pure function.

// IO is "allocated" so there is no way to construct an IO in the
// language -- it has to come from C.

module IO

interface {
    extern type IO (allocated);
}
