module Main

import Abstr;

interface {

    datatype Maybe<T> = Nothing | Just(T);

    const c1: Maybe<Abstr>;
      // OK at this point (error will be reported below when we try
      // to write an initializer for this constant)

    function main() { }
}

const c1: Maybe<Abstr> = Nothing;   // Error, initializer term mentions an abstract type.
const c2 = Nothing<Abstr>;    // Error, similarly.

const c3: i32 = {x=1, y=Nothing<Abstr>}.x;
  // Error, similarly (even though Abstr disappears after the initializer
  // term is evaluated to a normal form).

ghost const g1: Maybe<Abstr> = Nothing;  // OK (ghost)
ghost const g2 = Nothing<Abstr>;  // OK (ghost)
ghost const g3: i32 = {x=1, y=Nothing<Abstr>}.x;  // OK (ghost)

const c4: Maybe<Abstr> = Nothing;
  // Error - we still get the error even if there was no interface decl
  // for the constant.

const c5: Maybe<ExternType> = Nothing;
  // OK - extern type, not an abstract type.
