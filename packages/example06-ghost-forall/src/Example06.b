// Example 6 -- Ghost and Forall.

// In this example, we will talk about ghost variables and functions,
// and introduce the "forall" and "exists" keywords.

module Example06

interface {
    function main();
}


import Array;
import Console;

// The Int module provides constants like I32_MIN and I32_MAX, and functions
// like can_add_u32, can_sub_i8, etc.
import Int;


// Forall and Exists:

function fun1()
{
    // The "forall" keyword can be used to express the idea that some
    // Boolean expression is true for all values of a certain type.

    // For example, the following states that all values of type "bool"
    // are either true or false:
    
    assert forall (x: bool) x == true || x == false;


    // Similarly, "exists" says that there exists a value, of the given
    // type, for which some property is true.

    // For example, there exists a value x of type bool for which
    // "x && x" is true.

    assert exists (x: bool) x && x;


    // Note that "forall" and "exists" can only be used in verification
    // contexts (e.g., in an "assert", "requires" condition, etc),
    // not in executable code. The following would produce a compile
    // time error:

    // var b: bool = forall (x: i32) x == x;



    // Here is a simple statement about all integers that is easily verified.
    // It says that all integers of type u32 are either even or odd.

    assert forall (x: u32) (x % 2 == 0) || (x % 2 == 1);

    // Incidentally: the same statement about (x: i32) would be false,
    // because the % operator can return -1 for negative inputs. The
    // correct statement for x of type i32 is:

    assert forall (x: i32) (x % 2 == 0) || (x % 2 == 1) || (x % 2 == -1);



    // Sometimes we want to verify something about only a range of integers.
    // For this we can use the "==>" (implies) operator.
    
    // For example, let's say we want to verify that for all x between 2 and
    // 10, x is divisible by either 2, 3, 5, or 7. We would do this as follows:

    assert forall (x: i32) 2 <= x <= 10 ==>
        (x % 2 == 0) || (x % 3 == 0) || (x % 5 == 0) || (x % 7 == 0);

    // This could be read as: "For all x of type i32, if x is between 1 and 10,
    // then x is divisible by either 2, 3, 5 or 7".


    // Similarly, this states that x + x is equal to 2 * x, for all x within
    // the range I32_MIN/2 to I32_MAX_2:

    assert forall (x: i32) I32_MIN/2 <= x <= I32_MAX/2 ==> x + x == 2 * x;

    // Note that the range limit is necessary here. If we just wrote
    // "assert forall (x: i32) x + x == 2 * x", we would get an error that
    // the expressions "x + x" and "2 * x" might overflow the range of an i32.


    // Similar considerations apply with "exists". In this case the range is
    // limited by using "&&" rather than "==>". For example the following says
    // that there exists an x between 1 and 10 such that x is divisible by 2:

    assert exists (x: i32) 1 <= x <= 10 && x % 2 == 0;

    // (Read literally, this says "there exists an x such that x is between
    // 1 and 10, and x is divisible by 2.)


    // Again, this technique can be used to work around overflow issues. For
    // example if we wanted to prove there was a solution of the equation
    // x + 2 == 5, we could not just assert "exists (x: i32) x + 2 == 5",
    // because the expression "x + 2" would be considered invalid (it might
    // overflow). But if we knew the solution was between -1000 and 1000,
    // we could write:

    assert exists (x: i32) -1000 <= x <= 1000 && x + 2 == 5;


    // The "Int" module also contains functions like "can_mul_i32", 
    // "can_add_i8", "can_sub_u16", "can_div_u64", etc., which return 
    // true if a given multiplication, addition, subtraction, or division
    // can be carried out without overflow (or other error). 

    // Here are some examples of how these functions could be used:

    assert forall (x: i32) can_add_i32(x, x) ==> x + x == 2 * x;

    assert exists (x: i32) can_add_i32(x, 2) && x + 2 == 5;

    assert exists (x: i32) can_add_i32(x, 4) && can_mul_i32(x + 4, 3) && 3 * (x + 4) == 123;

    // Note that, just like the "forall" and "exists" operators, these
    // "can_xxx_yyy" functions can only be used in verification contexts,
    // not executable code. So for example, the following would be illegal:

    // var b: bool = can_add_i32(1, 2);
}


// Ghost Variables and Functions:

// It is possible to write a "ghost function". A ghost function does not exist
// at runtime and cannot be called while the program is running. Instead it
// can be used during verification.

// For example, the following ghost function returns true if a particular
// number is prime.

ghost function is_prime(p: i32): bool
{
    // p is prime if: (1) p >= 2; and
    // (2) for all numbers "n" strictly between 1 and p, p is not divisible
    // by n (i.e., p % n != 0).

    // Note that we are allowed to use "forall" here, because we are in a
    // ghost function (as already discussed, "forall" would not be allowed in 
    // normal executable code).

    return p >= 2 && 
        forall (n: i32) 1 < n < p ==> p % n != 0;
}

// We can use the ghost function in asserts, requires conditions, or similar
// "verification-only" contexts. For example, the following function has a
// precondition that it must be called on a prime number.

function fun2(p: i32)
    requires is_prime(p);
{
    print("fun2 called on ");
    print_i32(p);
    println(" which is prime");
}

// But the following function would not work, because it is not allowed to
// call a ghost function at runtime.

// function not_allowed(x: i32)
// {
//     if is_prime(x) {    // ERROR: calling ghost function from executable code
//         println("x is prime");
//     } else {
//         println("x is not prime");
//     }
// }


// The "fun2" function (above) can be used as follows:

function fun3()
{
    // This works -- the automated provers are able to show that 7 is prime.
    fun2(7);

    // They can even show that 1997 is prime, without any help.
    fun2(1997);

    // The following would NOT succeed, because 4 is not prime.
    // fun2(4);

    // The following would NOT succeed, because, even though I32_MAX happens
    // to be prime, it is too much to hope that z3 or any other solver would
    // be able to prove this by itself, without any help. Therefore the proof
    // will just time out, if you uncomment the following.
    // fun2(I32_MAX);

    // To re-iterate, we can call ghost functions from asserts, but not from
    // executable code:
    assert is_prime(13);   // this is allowed
    // var b: bool = is_prime(13);   // this is not allowed
}


function fun4()
{
    // As well as ghost functions, we also have the concept of ghost variables.
    // A ghost variable is just like a normal variable, except that it only 
    // exists at verification time: it does not actually exist when the program
    // is run. Computations involving ghost variables are not actually
    // executed -- they are only checked for validity by the verifier.

    // For example:

    ghost var b1 = is_prime(13);
    ghost var b2 = is_prime(4);

    // We can use ghost variables in asserts:

    assert b1;
    assert !b2;


    // We can update ghost variables by using a "ghost statement" as follows.

    ghost b1 = false;

    // We can NOT use ghost variables in executable code. The following would
    // fail, because the program is not able to "see" the value of the ghost
    // variable.
    // if b1 { println("b1 is true"); }


    // A ghost statement cannot modify a real variable (although a ghost
    // statement CAN observe the value of a real variable).

    var v = 1;
    ghost var g = 2;

    // ghost v = 2;      // not allowed, trying to modify real value from ghost statement
    ghost g = v + 1;     // allowed, this is only reading a real value from the ghost statement.


    // It is also possible to create ghost arrays.
    // Note that to allocate a ghost array, one uses the special
    // "alloc_ghost_array" function (which, unlike alloc_array, always 
    // succeeds and does not return a bool value). Also, ghost arrays do
    // not need to be freed when we are done with them.

    ghost var a: i32[*];     // create ghost array
    ghost alloc_ghost_array(a, 100);   // allocate 100 ghost integers
    ghost a[2] = 1;
    assert a[2] == 1;
}


function main()
{
    fun1();
    fun3();
    fun4();
}
