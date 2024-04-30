
# The "Babylon" programming language

"[Babylon](https://www.solarflare.org.uk/babylon)" is an experimental
new programming language that I am working on. The goal is to create a
low-level imperative-style language, similar to C, but with support
for program verification features (preconditions, postconditions and
so on).

Here is a simple example program written in the language.

    module Prime

    interface {
        // Define what is meant by a prime number.
        ghost function is_prime(n: i32): bool
        {
            return n >= 2 &&
                forall (i: i32) 2 <= i < n ==> n % i != 0;
        }

        // Declare a function which will check whether a number is prime.
        function check_if_prime(n: i32): bool
            ensures return <==> is_prime(n);
    }

    // The implementation of the "check_is_prime" function.
    function check_if_prime(n: i32): bool
        ensures return <==> is_prime(n);
    {
        if n < 2 {
            return false;
        }

        var i: i32 = 2;
        while i < n
            invariant 2 <= i <= n;
            invariant forall (j: i32) 2 <= j < i ==> n % j != 0;
            decreases ~i;
        {
            if n % i == 0 {
                return false;
            }
            i = i + 1;
        }

        return true;
    }

The interesting part of this example is the postcondition `ensures
return <==> is_prime(n)`. This basically states that
`check_if_prime(n)` should return true if and only if `is_prime(n)` is
true. The Babylon compiler will verify that this condition, along
with a number of other conditions (such as loop termination and
absence of run-time errors), is true.

This verification is done by formulating each of the conditions to be
checked as an SMT problem, and passing it to one or more external SMT
solvers to be proved. (Currently, we use
[z3](https://github.com/Z3Prover/z3), [cvc5](https://cvc5.github.io/)
and [vampire](https://vprover.github.io/).) If, for each condition, at
least one of the solvers responds with `unsat` (indicating that it has
found a proof), then we consider the program to be successfully
verified; otherwise an error is reported.


# Current Status

Be advised that this project is currently in a very early, pre-alpha
state. The language will change in incompatible ways in the future,
and you can expect bugs. Therefore I would not recommend anyone to use
this language for production purposes at this time. However, if anyone
wants to try out the language, and perhaps suggest improvements, they
would be welcome to do so.

The current status of the project is basically as follows:

 - There is a compiler (written in C) with "verify" and "compile"
   modes.
    - "Verify" mode takes one or more input files, formulates
      verification conditions, and uses SMT solver(s) to verify those
      conditions (as described above).
    - "Compile" mode works by translating the program to C files,
      which can then be compiled by any C compiler. (Previous versions
      produced assembly code directly, but I abandoned that approach
      since it was too complicated and had too many bugs.)

 - By default, the language verifies that various operator
   preconditions are satisfied (additions don't overflow, divisions
   don't divide by zero, array indexing is within bounds, memory
   allocations are eventually freed, etc.). This means that verified
   Babylon code shouldn't crash at runtime, or leak memory (at
   least in theory!).
    - The user can also add their own preconditions, postconditions
      and asserts, allowing further properties to be verified (e.g.
      state invariants, or perhaps even full functional correctness
      against some specification).
    - However, verification of more complex properties can be quite
      challenging, so I suspect most users would want to stick to
      "basic" verification (e.g. absence of run-time crashes, or
      simple state invariants), or perhaps doing more in-depth
      verification only on the most critical parts of their programs.

 - The language is reasonably complete, and it's certainly possible to
   write programs in it (see examples below). However, I am still
   tinkering with the language and its definition, and I expect to
   make backwards-incompatible changes in the future, so potential
   users should bear that in mind.

 - There is no standard library currently. To do I/O, one must write
   separate C functions, and then call those from the Babylon side.
   (Moreover, the C/Babylon interface isn't well documented, so you
   basically need to know something about how the compiler works, in
   order to write the C functions correctly.) Clearly this is not an
   ideal arrangement, but again, I hope to improve this in the future.

 - I have created a few example programs (see below), which
   demonstrate the system, and act as a tutorial of sorts.

 - There is no documentation yet (apart from this file and
   the example programs).


# Examples

The example programs are in the [examples](examples) folder.

Some highlights:

 - [Demo_07_Primes.b](examples/Demo_07_Primes.b) uses the Sieve of
   Eratosthenes to print out all prime numbers up to and including
   2^31 - 1. The program is verified (i.e. we include "assert"
   statements to check that the program prints all prime numbers in
   the given range, and nothing but prime numbers, and these asserts
   are verified by the SMT solvers).

 - [Demo_14_GCD.b](examples/Demo_14_GCD.b) implements Euclid's
   algorithm for finding the greatest common divisor of two numbers.
   Again, the program is verified by the SMT solvers to be a correct
   implementation.

 - The [chess](examples/chess) demo implements a simple interactive
   chessboard. This uses [SDL](https://www.libsdl.org/) to do the
   graphics and mouse input. The program consists of several Babylon
   modules which implement the game logic and UI, together with a
   small C file ("game_engine.c") which provides the interface to the
   SDL library.

![](examples/chess/screenshot.png)

*A screenshot of the chess demo. The Babylon compiler verifies that
this program cannot crash at runtime (or at least, the parts written
in Babylon cannot crash -- the program does also include some C code
which is unverified). We do not go so far as to verify that the
program is functionally correct, i.e. that the rules of chess are
correctly implemented -- but perhaps that could be a future project!*


# Building/Installing

This section describes how to build the Babylon compiler.

A Linux machine, with gcc (or another C compiler) available, is
required.

The Babylon compiler itself is written in C, and the only external
dependency is sqlite3. The simplest way to build is to run `gcc -O3 -o
babylon src/*.c -lsqlite3` to make an optimised `babylon` executable
in the current directory. (Ensure that you have the libsqlite3-dev
package, or equivalent for your OS, installed.)

(Alternatively, you can install the "Shake" build system from
https://shakebuild.com. Then you will be able to use the Shakefile.hs
that I created. This gives the ability to do incremental builds, as
opposed to a full rebuild. This is only really necessary if you intend
to work on the compiler itself, however -- the "gcc" command given
above probably works well enough for most users.)

As well as building the compiler, you will need to make sure that at
least one (and preferably all three) of the commands `z3`,
`cvc5-Linux` and `vampire` are available on your system. You might be
able to get pre-built binaries at the following links:
[z3](https://github.com/Z3Prover/z3/releases),
[cvc5](https://cvc5.github.io/downloads.html),
[vampire](https://github.com/vprover/vampire/releases). Otherwise they
can be built from source. Put the binaries into your search path
somewhere.

Note that the list of SMT solvers to use is currently hard coded into
the compiler (unfortunately). If you want to use different solvers (or
if they have different names on your system), look at
[src/fol.c](src/fol.c), and edit the `PROVERS` array and/or the
`NUM_PROVERS` define.

If you want to run the test suite you can just run the `run_tests.sh`
script. This looks for the compiler in `./build/babylon` (although you
can edit this at the top of the script) and it writes temporary files
into `test/output_tmp`.

For instructions on how to use the compiler, take a look at the
"Demo" programs in the [examples](examples) folder, and read the
comments. This will take you through the basics of the language and
explain how to use the compiler and verifier.



# Future work

The [project webpage](https://www.solarflare.org.uk/babylon) includes
a "Future work" section giving details of possible future directions
for this project.


# Related projects

Here is a (non-exhaustive) list of programming languages and other
tools that can be used for software verification (or theorem proving
more generally). These are in no particular order.

 - [Dafny](https://dafny.org/)
 - [SPARK](https://en.wikipedia.org/wiki/SPARK_(programming_language))
 - [Frama-C](http://frama-c.com/index.html)
 - [VCC](https://www.microsoft.com/en-us/research/project/vcc-a-verifier-for-concurrent-c/)
 - [Eiffel](https://en.wikipedia.org/wiki/Eiffel_(programming_language))
 - [Whiley](https://whiley.org/)
 - [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/)
 - [Agda](https://github.com/agda/agda)
 - [Isabelle](https://isabelle.in.tum.de/)
 - [Coq](https://coq.inria.fr/)
 - [Lean](https://lean-lang.org/)

A brief discussion of some of these can be found on the [project
webpage](https://www.solarflare.org.uk/babylon) under the "Related
projects" section.


# Disclaimer

For the avoidance of doubt: this project is currently considered an
experimental prototype, not a fully working system, and is provided
WITHOUT WARRANTY OF ANY KIND.


# Contact

I can be contacted by email at: stephen (at) solarflare.org.uk.

Project website link: https://www.solarflare.org.uk/babylon
