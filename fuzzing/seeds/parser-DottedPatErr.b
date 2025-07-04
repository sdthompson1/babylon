// Qualified ("dotted") ctor name in pattern, but with nothing after the dot.

module DottedPatErr
interface {
  const x: i32 =
    (match (1) { case Foo. => 2 });
}
