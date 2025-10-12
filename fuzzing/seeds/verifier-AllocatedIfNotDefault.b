module Main

interface {}

import Test;

// Define an abstract type which counts as "allocated" if it is not equal to the default.
// Also define some extern functions which allocate and deallocate it.

extern type MyType (allocated);

extern function alloc_mytype(ref x: MyType)
    requires !allocated(x);
    ensures allocated(x);

extern function free_mytype(ref x: MyType)
    requires allocated(x);
    ensures !allocated(x);

function g1()
{
    var x: MyType;    // OK, default is not allocated.
    free_mytype(x);     // Error, precondition fails
}

function g2()
{
    var x: MyType;
    alloc_mytype(x);
    // Error: x has not been freed
}

function g3()
{
    var x: MyType;
    alloc_mytype(x);
    free_mytype(x);
    // OK: x has been successfully freed
}
