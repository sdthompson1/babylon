module Main
interface {}

  datatype Mono = Mono1 { x: i32, y: bool } | Mono2 { z: i32 };

  datatype Poly<a,b> = Poly1 { p: a } | Poly2 { r: a, s: b, t: a };

  datatype Numbered = N1 { i32, bool } | N2;

  function f0()
  {
  }

  function f1()
  {
    var m1: Mono = Mono1 { x=1, y=false };   // ok
    var m2: Mono = Mono1 { x=1, y=2 };       // error, wrong type for y
    var m3: Mono = Mono2 { x=1, z=3 };       // error, x does not exist
    var m4: Mono = Mono1 { x=1, y=true, x=2 };   // error, x appears multiple times
    var m5: Mono = Mono1;                    // error, fields missing. (get "can't use function as value" because Mono1 is considered a function.)
    var m6 = Mono1;                          // error, fields missing
    var x = f0 { x=1 };                   // error, can't call f0 in this way
  }

  function f2()
  {
    var p1: Poly<i32,Mono> = Poly1<i32,Mono> { p=100 };    // ok
    var p2: Poly<i32,Mono> = Poly1<i32,Mono> { 100 };      // error, field name wasn't given
    var p3: Poly = Poly1<i32,Mono> { p=100 };              // error, missing type arguments
    var p4: Poly<i32,Mono> = Poly1 { p=100 };              // ok, Poly1<i32,Mono> is inferred
    var p5: Poly<i32,Mono> = Poly2<i32,Mono> { r=1, s=Mono2{z=100}, t=3 };    // ok
    var p6: Poly<i32,Mono> = Poly2<i32,Mono> { s=Mono2{z=false}, r=1, t=3 };  // error, type mismatch (z)
    var p7: Poly<i32,Mono> = Poly2<i32,Mono> { s=99, r=1, t=3 };              // error, type mismatch (s)
    var x = (1+true) {1,2,3};       // error, LHS doesn't typecheck
  }

  function f3()
  {
    var n1: Numbered = N1 { 100, 200 };    // error, type mismatch in field '1'
    var n2: Numbered = N2;                 // ok
  }

  const notfound         = {x=1}.z;  // error, not found
  const badrecord        = 1234.a;   // error, can't take fields of a number
  const badlhs           = (1.a).b;  // also error







  // Duplicate field name
  datatype T6 = T6 { field1: i32, field1: i32 };

  datatype T7 = T71 { field1: i32 } | T72 { field1: i32, field2: i32 };
         // No problem, duplicating in different ctors is allowed
