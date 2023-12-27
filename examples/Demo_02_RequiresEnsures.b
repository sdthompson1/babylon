
// This is the second demonstration program for the Babylon language.

// In this file we explain the concept of function preconditions
// and postconditions.


module Demo_02_RequiresEnsures

interface {
    // First some examples of "plain" functions that don't have any
    // preconditions or postconditions.

    // (Recall that we are just specifying the module interface at this point.
    // This means we don't have to give the full implementation of the functions
    // just yet -- we can give only the function names and types, and leave the
    // implementation until later. That is what we will do here.)


    // This first function takes two values "x" and "y" of type "i32" and
    // returns another value of type "i32".
    // Note: "i32" refers to a signed 32-bit integer, that is to say,
    // an integer between -2147483648 and +2147483647 inclusive.
    function fun1(x: i32, y: i32): i32;

    // Here is a function that takes an "i32" but doesn't return any value.
    function fun2(x: i32);


    // This next function has a precondition (or "requires" clause).
    // A precondition is simply a Boolean expression that must be true
    // whenever the function is called.
    //
    // In this case, the requirement is that the argument should be between
    // -1000 and 1000 inclusive.
    //
    // When the verifier runs, it will check all calls to the "fun3" function
    // to make sure that this requirement is complied with. If "fun3" is ever
    // called with an argument outside the -1000 to +1000 range (or if the
    // SMT solvers are not able to find a proof that this is the case) then
    // the program will be rejected.
    //
    function fun3(x: i32): i32
        requires -1000 <= x <= 1000;


    // This function has a postcondition (or "ensures" clause).
    // A postcondition is a Boolean expression that is guaranteed to be
    // true when the function returns.
    //
    // The Babylon verifier checks all function definitions to make sure
    // that they comply with the stated postcondition(s).
    //
    // In this case, the function "fun4" expects both its arguments to
    // be between 0 and 100, and it promises that its return value will
    // be between 0 and 200. (Note the use of the keyword "return" in
    // the "ensures" clause to signify the value that will be returned
    // from the function.)
    //
    function fun4(x: i32, y: i32): i32
        requires 0 <= x <= 100;
        requires 0 <= y <= 100;
        ensures 0 <= return <= 200;


    // We will also write a small "main" function to demonstrate the above.
    function main();
}


// ExampleLib will be needed:
import ExampleLib;


// Here are the implementations of fun1 and fun2.

function fun1(x: i32, y: i32): i32
{
    print_string("This is fun1\n");
    return x;
}

function fun2(x: i32)
{
    print_string("fun2 was called with: ");
    print_i32(x);
    print_string("\n");
}


// Here is the implementation of fun3.

// Note that the "requires" condition must be given again in the
// implementation.

function fun3(x: i32): i32
    requires -1000 <= x <= 1000;
{
    // Here we will code fun3 to return its argument, plus 10.

    // Any time there is a "+" operator (or other arithmetic operator),
    // the verifier will try to prove that the operator does not overflow
    // (i.e., in this case, the result is in the range -2147483648 to
    // +2147483647, as appropriate for an i32).

    // In this case, what basically happens is that the Babylon compiler
    // sends the following problem to the SMT solvers:

    // "Let x be an integer; assume that -1000 <= x <= 1000; now prove
    // that "-2147483648 <= x + 10 <= 2147483647." 

    // The solver can respond with three possible results: "unsat" (which
    // means a proof was found), "sat" (which means the prover thinks it has 
    // found a counterexample), and "unknown" (which means the prover has given
    // up trying to find a proof). There is also a fourth possibility, which is
    // that the solving process could time out, without giving a result. (By 
    // default the compiler allows the solver process to run for 60 seconds
    // before killing it.)

    // The Babylon compiler also runs several different provers (currently z3, 
    // cvc5 and vampire) in parallel. (This is because they all have different
    // strengths and weaknesses, so sometimes one prover might find a solution
    // where the others do not.) So long as at least one of the solvers responds
    // saying that it has found a proof, then the theorem is accepted as being 
    // true.

    // (Of course, this does mean that one has to trust that the external
    // prover tools are giving the correct results...)

    // In this case, the theorem that "x + 10" is in the correct range is very
    // easy to prove, and the solvers quickly return a "proof found" ("unsat")
    // result, and so the program is accepted.

    return x + 10;

    // The reader might like to remove (or modify) the "requires" condition
    // and then see what happens when the program is verified. (Instructions
    // for running the verifier are given at the bottom of this file).
}


// Here is the implementation of fun4.

function fun4(x: i32, y: i32): i32
    requires 0 <= x <= 100;
    requires 0 <= y <= 100;
    ensures 0 <= return <= 200;
{
    // We will code this function to return the sum of x and y.

    // In this case, when the Babylon verifier is run, it will ask the 
    // solvers to do two proofs. First, that the sum x + y does not overflow
    // the range of an i32. And second, that the postcondition
    // "0 <= return <= 200" is satisifed.

    // In that second case, the solver is basically told "let x, y and r be
    // integers; assume that 0 <= x <= 100, and 0 <= y <= 100, and r = x + y;
    // now prove that 0 <= r <= 200". Again this is not a difficult proof, 
    // and the solvers will succeed.

    return x + y;

    // Again, the reader might like to try changing something to try
    // to make the verification fail. For example, changing the return
    // statement to "return x + 2*y;" will cause a failure.
    // (The "+" and "*" operators will verify successfully -- it is clear
    // that these cannot overflow, because x and y are both between 0 and
    // 100 -- but the return statement itself will fail to verify, because 
    // it does not meet the stated postcondition.)
}


// A small demo program.

function main()
{
    // Variables can be declared with the "var" keyword.
    // Here we assign the result of fun1 to a variable "a" (of type i32).
    var a: i32 = fun1(1, 2);

    print_string("The value of a is ");
    print_i32(a);
    print_string("\n");

    // Now let's try fun2.
    fun2(25);

    // Now let's try fun3.
    // When we call fun3, the Babylon verifier will ask the automatic provers
    // to confirm that the function precondition is satisfied, i.e., that
    // -1000 <= 123 <= 1000 (in this case). 
    // Clearly the solvers will have no trouble proving this. (If you want, you
    // could try changing the "123" below to a value outside the -1000 to 1000
    // range, and see what error message is produced.)

    var b: i32 = fun3(123);

    print_string("The value of b is ");
    print_i32(b);
    print_string("\n");

    // Finally, let's try fun4 which should add its two arguments.
    var c: i32 = fun4(10, 20);
    
    print_string("The value of c is ");
    print_i32(c);
    print_string("\n");
}


// In order to verify this program, try the following command:

// babylon -V Demo_02_RequiresEnsures.b

// This will print a lot of progress messages -- the important thing to
// look for is the bottom line which will either say "Verification successful"
// or "Verification failed". In the latter case, look at the line just above 
// to see the actual error message.


// In order to actually run the program, use the following sequence of 
// commands:

// babylon -c Demo_02_RequiresEnsures.b
// gcc Demo_02_RequiresEnsures.s ExampleLib.s example_lib.c
// ./a.out



// *** Note: "-v" vs "-V" options

// Running babylon with "-V" (upper case) will verify the given
// module AND all modules imported by it. By contrast, "-v" will verify
// the given module ONLY. In large projects, it can be useful to use "-v"
// just to verify the module that one is currently working on, as this will be
// quicker than verifying the whole program. But it is still recommended to
// verify the whole program (using "-V" on the top level module) every so
// often, as this is the only way to confirm that there are no errors in
// the program overall.


// *** Note: Verification cache

// In larger projects the verification process can take some time to run.
// Therefore, a caching feature is provided. This works by caching
// verification results in a file called "babylon.cache" on disk. (This
// file is stored in the same folder as the source module(s) being
// compiled, unless you are using the "-o" option to set an output 
// directory, in which case the cache file is stored there.) This file
// persists between different runs of the compiler.

// The cache works at two levels. Firstly, every time a module is successfully
// verified, a hash of the entire source text of the module (together with its
// dependencies) is stored in the database. This means that when re-verifying 
// a large program (consisting of many modules), only the modules that changed
// (and their dependent modules) need to be re-verified, saving time.

// Secondly, each time the SMT solver is invoked, and a successful result is
// obtained, a hash of the SMT problem description is stored in the database.
// This means that if the same SMT problem is encountered in future, the SMT
// solver will not need to be re-invoked. This means that even if a module
// file has been changed, typically only a subset of the verification work
// will have to be re-done.

// The combination of these two features saves a great deal of time in the 
// common case where one is making incremental changes to one or two modules
// in a large project, then re-running the verifier.

// The cache is enabled automatically, and the babylon.cache file is created
// automatically if it does not currently exist.

// Of course, some users might not trust the caching implementation, or might
// not want to use the cache for other reasons. Therefore, a "--no-cache" option
// is provided. If this is used, the compiler will ignore any existing babylon.cache 
// file and will not create a new one. This will make the verification result more
// "reproducible" (as it will not depend on state left behind by previous runs)
// but the trade-off is that runtimes will likely be much higher.

// It is also always safe to manually delete the babylon.cache file. The compiler
// will just re-create it the next time it is run (unless "--no-cache" was used).
