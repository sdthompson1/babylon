module Allocated

interface {}

import Test;

function f1(x: i32[*])
{
    var y = x;    // Error, copying from (possibly) allocated variable
    return;       // Error, y still allocated
}

function f1a(x: i32[*])
{
    var y: i32[*];
    y = x;        // Error, copying from (possibly) allocated variable
}                 // Error, y still allocated

function f2()
{
    var x: i32[*];
    var y: i32[*];
    resize_array<i32>(x, 100);
    x = y;        // Error, copying to an allocated variable
}

function f3(ref x: i32[*]): i32[*]
{
    return x;  // Error, returning possibly allocated variable
}

function f4(): i32[*]
{
    var x: i32[*];
    return x;     // Returning an empty array is OK
}

function f5()
{
    var x: i32[*];
    resize_array<i32>(x, 10);
    // Error, x still allocated
}


// testing the 'allocated' keyword
ghost function f6()
{
    assert allocated(1) == false;

    var x: i32[*];
    assert allocated(x) == false;
    
    resize_array<i32>(x, 100);
    assert allocated(x) == true;

    // note: no error that x still allocated, because this
    // is a ghost function
}

ghost function f7()
{
    assert allocated(1) == true; // Negative test
}

ghost function f8()
{
    assert allocated(1/0);   // with the new "parallel jobs" system this now reports error on both the "1/0" and the assert (it doesn't wait to see if 1/0 fails before starting the assert check!).
}


// Allocated 'extern' types.
extern type Foo (allocated);

datatype MaybeFoo = Nothing | Just(Foo);

ghost function f9()
{
    var v: Foo;  // allowed because we are in ghost function

    assert allocated(v);
    assert allocated(Just(v));
    assert !allocated(Nothing);
}











// Returning allocated() from a function
ghost function is_allocated<T>(x: T): bool
{
    return allocated(x);
}

ghost function f11(f: Foo)
{
    assert !is_allocated<i32>(0);
    assert is_allocated<Foo>(f);
    assert !is_allocated<Foo>(f);  // negative test
}

// Copying is allowed in ghost function
ghost function f12(x: i32[*])
{
    var y: i32[*];
    y = x;              // OK (assign from maybe-allocated value)

    var z: i32[*] = x;   // OK (init from maybe-allocated value)

    match x {
    case xx => y = xx;  // OK (assign from maybe-allocated value within a match)
    }
}
