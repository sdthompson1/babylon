
// This is the twelfth demonstration program for the Babylon language.

// In this file we introduce generic functions and types.


module Demo_12_Generics

interface {
    function main();
}

import ExampleLib;


// Sometimes we want to use a function at several different types. For
// example, here is a definition of the identity function (the function
// that just returns its own argument). This can work at any type T.

function id<T>(x: T): T
    requires !allocated(x);
{
    return x;
}

// Note several things:

//  - The syntax <T> means that this function is generic and has one "type
//    parameter", T. The idea is that T can stand for any other type, for
//    example we could have id<i32> which returns an integer, or id<bool>
//    which works on bools, and so on.

//  - The parameter x is declared in the usual way except that its type is
//    T instead of a specific named type. Similarly the return type is
//    specified as T.

//  - The function has a precondition !allocated(x). This is necessary
//    because there is nothing to stop T being an array type (for example)
//    and then the statement "return x" would be illegal, because (as
//    discussed in the previous demo) it is not allowed to return an allocated
//    value. If id was used at type i32 or bool (say), this precondition would
//    be trivially satisfied, because all i32s and bools are non-allocated; but
//    if id was used at an array type, this precondition would actually do
//    something (it would mean that the parameter must be an empty array).


// Let's show how to use the id function.

function fun1()
{
    // When calling a generic function, we must specify the type being used
    // in < > brackets. Here we call the id function with type i32:
    var i = id<i32>(100);
    
    print_i32(i);   // prints 100
    print_string("\n");

    // Note: in other languages (like Java or C++) the < > brackets are not
    // required when calling a generic function -- only when defining it.
    // In other words the Java or C++ compiler can figure out what "T" is,
    // simply by looking at the argument that was passed.
    // However, the Babylon compiler is not that smart (yet) so, for now, the
    // type parameters must always be explicitly given when calling a
    // generic function.

    // We can also try the id function at other types:
    
    var b = id<bool>(false);
    assert b == false;

    var a1: i32[*];           // An empty array
    var a2 = id<i32[*]>(a1);  // Works, a2 is now an empty array as well.

    // (If a1 was not empty, then the call id<i32[*]>(a1) would be rejected
    // by the verifier.)
}


// We can also define generic types.

// The following defines a "Maybe" type which has two values, "Just" (carrying
// a value of type T) and "Nothing" (which carries no value).

datatype Maybe<T> = Just(T) | Nothing;


// Generic functions are often useful in conjunction with generic types.
// The following function returns true if it is given a Just value, false
// otherwise.

function is_just<T>(x: Maybe<T>): bool
{
    match x {
    // Note: there is no need to write <T> after the constructor names
    // in "case" patterns.
    case Just(_) => return true;
    case Nothing => return false;
    }
}

function fun2()
{
    // When *creating* a generic value (as opposed to in "case" patterns) we do
    // need to give the < > brackets. For example:

    var m1: Maybe<i32> = Nothing<i32>;
    var m2: Maybe<i32> = Just<i32>(100);

    if is_just<i32>(m1) {
        print_string("m1 is just\n");
    }
    if is_just<i32>(m2) {
        print_string("m2 is just\n");
    }
}


function main()
{
    fun1();
    fun2();
}


// To verify this example:
//   babylon -V Demo_12_Generics.b

// To run this example:
//   babylon -c Demo_12_Generics.b
//   gcc Demo_12_Generics.c ExampleLib.c example_lib.c
//   ./a.out
