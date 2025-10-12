module Main
interface {
  function f()
  {
    match (1) {
      case ref A =>    // Error, A is a constructor not a variable.
    }
  }
}

