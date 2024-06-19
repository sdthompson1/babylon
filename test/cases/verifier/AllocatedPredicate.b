module AllocatedPredicate

interface {}

import Test;

// Define an abstract type which counts as "allocated" if it is not equal to the default.
// Also define some extern functions which allocate and deallocate it.

type MyType
    allocated(x) if x != default();

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


// Here we try to define a type that is allocated if and only if it is not allocated.
// This doesn't cause any contradiction (basically, the verifier handles this by replacing
// the "inner" use of allocated(x) with some arbitrary boolean constant).
// (TODO: This example should ideally produce some kind of error or warning message instead.)

type BadType
    allocated(x) if !allocated(x);

function g4()
{
    // The following is an error because we can't prove whether default<BadType>()
    // is allocated or not. (In particular: there is not an automatic proof by contradiction.)
    var x: BadType;
}


// A sneakier version, where the allocated(x) is "hidden" inside a ghost function.

ghost function is_alloc<T>(x: T): bool
{
    return allocated(x);
}

type VeryBadType
    allocated(x) if !is_alloc<VeryBadType>(x);

function g5()
{
    var x: VeryBadType;   // Error: can't prove !allocated(default<VeryBadType>()).
}
