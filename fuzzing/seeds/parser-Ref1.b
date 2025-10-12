module Main
interface {
  function f()
  {
    match (1) {
      case {ref {}} =>     // Error, "ref" must be followed by a variable name.
    }
  }
}

