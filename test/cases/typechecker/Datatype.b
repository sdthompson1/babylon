module Datatype
interface {}

  datatype Color = Red | Green | Blue;




  datatype Maybe<a> = Just{a} | Nothing;

  datatype Recursive = R1 | R2{Recursive};    // error, illegal recursion

  datatype BadFieldType = BadFieldType { Maybe };    // error, wrong number of type args


  function foo()
  {
    var a: Color = Blue;     // ok
    var b: Color = 100;      // error
    var c: i32   = Red;      // error

    Green = Blue;            // error, not an lvalue
  }

  function bar<a>(m: Maybe<a>)
  {
    var m2: Maybe<a>   = m;    // ok
    var m3: Maybe<i32> = m;    // error
    var m4: Maybe<a,a> = m;    // error, wrong num tyargs
    var m5: Maybe;             // error, wrong num tyargs
    var m6 = Nothing;          // now works - infers a type-argument
  }

  function call_bar()
  {
    bar<i32>(Nothing<i32>);
    bar<bool>(Nothing<bool>);
    bar<i32>(100);             // error

    bar<i32>(let n = Nothing in n);        // works, infers Nothing<i32>
    bar<i32>(let n = Nothing<i32> in n);   // ok
    bar<i32>(let n = Nothing<u32> in n);   // error, type mismatch

    bar<Maybe>(100);           // error, wrong num tyargs
    bar(Nothing<i32>);         // works, infers bar<i32>
    foo<i32,i64>();            // error, no tyargs expected
  }

  const c1: Maybe = 100;                 // error, wrong num tyargs
  const c2: Maybe<Maybe> = 100;          // error, wrong num tyargs
  const c3: Maybe<Maybe<Maybe> > = 100;  // error, wrong num tyargs (note syntax!)
  const c4 = Nothing;                    // works, infers a type-argument
  const c5: Maybe<i32> = Red;            // error, type mismatch


  // equality, comparison operators
  const eq1: bool = Red == Red;    // error, not allowed in exec code (yet?)
  const eq2: bool = Red < Green;   // error, < doesn't work on "enums"
  const eq3: bool = Red != Nothing<i32>;   // type mismatch
  const eq4: bool = call_bar == call_bar;  // error, functions can't be used as values

  function eqtest()
  {
    assert (Red == Red);    // ok in ghost code
    assert (Red < Green);   // error
    assert (Red != Nothing<i32>);   // error
    assert (call_bar == call_bar);  // error, functions can't be used as values
  }
