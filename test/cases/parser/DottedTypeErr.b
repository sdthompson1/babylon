// Qualified ("dotted") name in type, but with nothing after the dot.

module DottedTypeErr
interface {
    const x: M. = 100;
}
