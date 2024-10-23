module Datatypes
interface {}

import Test;

datatype D<a> = D { a };

function return_one<a> (x: D<a>): i32
{
    return 1;
}

function foo(x: D<i32>)
{
    assert (return_one<i32>(x) == 1);   // ok
    assert (return_one<i32>(x) == 2);   // error
}


datatype Simple<a> = Simple;
function simple()
{
    assert (let s = Simple<i16> in true);     // ok
}


datatype Color = Red | Green | Blue;
function test_eq()
{
    assert (Red == Red);
    assert (Red != Green);
    assert (Simple<i32> == Simple<i32>);
    assert (Red == Green);  // error
}


//
// Various default-init cases
//

function default_init()
{
    var c: Color;
    assert (c == Red);
    assert (c != Red);  // fails
}

function default_init_2()
{
    var s: Simple<i32>;
    assert (s == Simple<i32>);
    assert (s != Simple<i32>);   // fails
}

function default_init_3()
{
    var a: D<bool>;
    var b: D<bool>;
    assert (a == b);
    assert (a != b);   // fails
}

function default_init_4<T: Default+Copy>()

{
    var a: T;
    var b: T;
    assert (a == b);
    assert (a != b);   // fails
}

function default_init_5()
{
    var a: D<Simple<Color>>;  // single '>>' token, parser must split into '>' and '>'
    var b: D<Simple<Color> >; // two separate '>' tokens
    assert (a == b);
    assert (a != b);   // fails
}
  
function default_init_shadow<Color: Default+Copy>()

{
    var a: Color;
    var b: Color;
    assert (a == b);
    assert (a != b);   // fails
}
