module Main
interface {}
  function f1(
               y: {f1: i8, f1: i8} )    // Error: duplicate fieldname
  {
  }

  function f2()
  {
    match ({x=1, y=2}) {

      case {x=p1, x=p2} =>       // Error: duplicate fieldname
      case {z=99} =>             // Error: 'z' not found
    }

    match ({1,2}) {
      case {a,b,c} =>      // Error: too many fields in pattern
      case {a} =>          // Error: not enough fields in pattern
      case {a,b} =>        // Just right!
    }
  }


  datatype D = A | B{};

  function f3()
  {
    var x1 = A;     // OK
    var x2 = A{};   // Error
    var x3 = B;     // Error ("can't use function as a value")
    var x4 = B{};   // OK
  }
