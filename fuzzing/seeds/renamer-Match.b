module Main
interface {
  const x =
    match ({1,2}) {
      case {x,x} => 0     // Error: duplicate definition
      case Name => 0      // Error: not in scope 'Name' (initial capital = ctor)
      case name => name   // This is ok (initial lower case = variable)
    };
}
