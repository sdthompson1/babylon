
// This is the eighth demonstration program for the Babylon language.

// Here we will talk a bit about the "ref" (reference) feature.


module Demo_08_Refs

interface {
    function main();
}

import ExampleLib;


// Normally functions are not allowed to modify their arguments (an attempt
// to do so will produce a compile time error). However, if an argument is
// marked "ref" then it can be changed in the function. The change will be
// reflected in the caller. For example, the following function sets its
// argument to 100:

function change_to_100(ref x: i32)
{
    x = 100;
}

// To use it we can do the following:

function fun1()
{
    var x = 10;
    change_to_100(x);   // x is now magically 100
    print_i32(x);       // prints 100
    print_string("\n");
}


// In postconditions, any mention of a "ref" argument refers to the new
// value of the variable (after the function has run). The old values can
// be referred to by using the "old" keyword, as shown below.

// This function sets its first argument to the sum of the two inputs,
// and its second argument to the product of the two inputs.
// (For simplicity we restrict the inputs to the range 0 to 1000.)

function sum_and_product(ref x: i32, ref y: i32)
    requires 0 <= x <= 1000;
    requires 0 <= y <= 1000;

    // After the function runs, x will equal the sum of the two inputs
    ensures x == old(x) + old(y);

    // After the function runs, y will equal the product of the two inputs
    ensures y == old(x) * old(y);
{
    var sum = x + y;
    var prod = x * y;

    x = sum;
    y = prod;
}


// Let's see how it works:

function fun2()
{
    var x: i32 = 10;
    var y: i32 = 20;
    sum_and_product(x, y);

    print_i32(x);  // prints 30
    print_string("\n");
    print_i32(y);  // prints 200
    print_string("\n");


    // There is one very important restriction which is that reference
    // arguments are not allowed to alias each other. For example the
    // following is forbidden:
    // sum_and_product(x, x);

    // The verifier will flag up an error if you uncomment the line above.

    // The reason for this restriction is just to simplify the verification
    // process. If two "ref" variables might refer to the same underlying
    // variable then verification would become a lot more complicated.
}


// It's allowed for a function with ref arguments to also return a value:
function test_ref_and_return(ref x: i32): bool
{
    if x > 100 {
        x = 1234;
        return true;
    } else {
        return false;
    }
}

function fun3()
{
    var x: i32 = 250;

    // There is another restriction which is that any function call that
    // takes "ref" arguments must immediately be assigned to a variable.
    // It cannot be used in an "if" test, or as a subexpression in any
    // other expression, or anywhere else.

    // For example the following is not allowed:
    // if test_ref_and_return(x) { ... do something ... }

    // Instead we have to do this:
    var b = test_ref_and_return(x);
    if b {
        print_i32(x);         // prints 1234
        print_string("\n");
    }
}


// Now let's see a quick example of "ref" and "forall" being used together.

// This function will clear an array to all-zeroes. We write some
// "ensures" conditions to specify that the function will clear all elements
// of the array (without resizing the array).

// The condition "all elements of array are zero" may be stated as
// "forall (i: u64) i < sizeof(a) ==> a[i] == 0"
// (i.e. whenever "i" is a valid array index, a[i] is zero).

// The condition that the size should not change can be written as
// "sizeof(a) == old(sizeof(a))". Note this could equivalently be written
// "sizeof(a) == sizeof(old(a))" (it makes no difference).

function clear_array(ref a: i32[])
    ensures sizeof(a) == old(sizeof(a));
    ensures forall (i: u64) i < sizeof(a) ==> a[i] == 0;
{
    // To do this we use a while-loop.

    // One of the invariants will be that the size of the array equals its
    // original size. Unfortunately it is not allowed to use "old" outside
    // of a postcondition, so we cannot simply write "invariant 
    // sizeof(a) == old(sizeof(a))".

    // The solution is to save the original size of the array into a ghost
    // variable.

    ghost var old_size = sizeof(a);

    // We can now write our loop.
    
    var i: u64 = 0;
    while i < sizeof(a)
        decreases ~i;

        // The loop does change a, but it doesn't change sizeof(a).
        invariant sizeof(a) == old_size;

        // i remains in the range 0 to sizeof(a) (it will equal sizeof(a)
        // after the final loop iteration).
        invariant i <= sizeof(a);

        // After i iterations, the first i elements will be zero.
        invariant forall (j: u64) j < i ==> a[j] == 0;
    {
        // The loop itself just sets a[i] to zero, then increments i.
        a[i] = 0;
        i = i + u64(1);
    }

    // At this point, i == sizeof(a) and the last invariant is therefore
    // forall (j: u64) j < sizeof(a) ==> a[j] == 0,
    // which is exactly what we need to prove the correctness of the loop.
    // Therefore, we are done.
}


// There are actually two uses of "ref". The first (already shown above) is
// reference arguments to functions. The second is reference variables, that
// is, variables declared using "ref" instead of "var". This is demonstrated
// below.

function fun4()
{
    var i: i32 = 10;

    // Here we create a reference variable "r1", and set it to
    // be a reference to "i".

    // This means that any future usage of r1 will actually be treated
    // as a reference to i instead.

    ref r1 = i;

    // We can then modify i "through" r1 as follows.
    r1 = 20;

    // i is now equal to 20.
    print_i32(i);   // prints 20
    print_string("\n");
}


function main()
{
    fun1();
    fun2();
    fun3();
    fun4();
}


// To verify this example:
//   babylon -V Demo_08_Refs.b

// To run this example:
//   babylon -c Demo_08_Refs.b
//   gcc Demo_08_Refs.c ExampleLib.c example_lib.c
//   ./a.out
