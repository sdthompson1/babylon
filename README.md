
# The "Babylon" programming language

"Babylon" is an experimental new programming language that I am
working on. The goal is to create a low-level imperative-style
language, similar to C, but with support for program verification
features (preconditions, postconditions and so on).

Here is a simple example program written in the language.

    module Prime

    interface {
        // Define what is meant by a prime number.
        ghost function is_prime(n: i32): bool
        {
            return n >= 2 &&
                forall (i: i32) 2 <= i < n ==> n % i != 0;
        }

        // Export a function to check whether a number is prime.
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
return <==> is_prime(n)` which is attached to the `check_is_prime`
function. This basically states that `check_if_prime(n)` should return
true if and only if `is_prime(n)` is true. The Babylon verifier will
confirm that this condition, along with a number of other conditions
(such as loop termination and absence of run-time errors), is true.

This verification is done by formulating each of the conditions to be
checked as an SMT problem, and passing it to one or more external SMT
solvers to be proved. (Currently, we use
[z3](https://github.com/Z3Prover/z3), [cvc5](https://cvc5.github.io/)
and [vampire](https://vprover.github.io/).) If, for each condition, at
least one of the solvers responds with `unsat` (indicating that it has
found a proof), then we consider the program to be successfully
verified; otherwise an error message is reported.


# Current Status

The first thing to say is that this project is still at a very early
and experimental stage. I would not recommend anyone to use this
language for "production" purposes yet -- the language itself is
likely to change, and there are probably bugs in the compiler.
However, if anyone would like to experiment with the language, and
perhaps suggest improvements, they would be welcome to do so.

The current status of the project could be summarised as follows.

 - There is a working compiler, written in C, with "verify" and
   "compile" modes. "Verify" works by formulating SMT problems, as
   described above. "Compile" works by producing assembly code files,
   which can then be assembled and linked to make an executable.
   (Currently the assembly code produced is rather inefficient, and
   also only x86-64 running on Linux is supported. This should be
   improved in future.)

 - The language itself is reasonably complete, and it's possible to
   write programs in it, but I think it's fair to say that there are
   still a lot of new features and improvements that could be added,
   in order to make programming more convenient. (To give one example,
   there is no "for" loop in the language currently; one has to use
   "while" loops instead.)

 - There is also, at the moment, no "standard library" provided. So
   for example, there is not even a "print" function available. It
   *is* possible to link C functions with the Babylon program, and in
   practice, this is what one has to do, if one wants to do any kind
   of I/O. (Clearly this is something that should be improved in the
   future, but I think this arrangement works reasonably well for
   now.)
      
 - There is no documentation yet. We do have a series of example
   programs, with comments, that explain some of the language
   features. Hopefully people can at least get an idea of how things
   work by studying these examples. (Proper documentation will be
   provided later, once the language has stabilised a bit more.)



# Examples

The example programs are in the [examples](examples) folder.

Some highlights:

 - [Demo_07_Primes.b](examples/Demo_07_Primes.b) uses the Sieve of
   Eratosthenes to print out all prime numbers up to and including
   2^31 - 1.

 - [Demo_14_GCD.b](examples/Demo_14_GCD.b) implements Euclid's
   algorithm for finding the greatest common divisor of two numbers.

 - The [chess](chess) demo implements a simple interactive chessboard.
   This uses [SDL](https://www.libsdl.org/) to do the graphics and
   mouse input. The program consists of several Babylon modules which
   implement the game logic and UI, together with a small C file
   ("game_engine.c") which provides the interface to the SDL library.

![](examples/chess/screenshot.png)

*A screenshot of the chess demo. The Babylon compiler verifies that
this program cannot crash at runtime. We do not go so far as to verify
that the rules of chess are correctly implemented (according to some
formal specification), but perhaps that could be a future project!*


# Building/Installing

This section describes how to build the Babylon compiler.

A Linux machine, with gcc (or another C compiler) available, is
required.

The Babylon compiler itself is written in C, with no external
dependencies, so it is easy to build. You can just run `gcc -O3 -o
babylon src/*.c` to make an optimised `babylon` executable in the
current directory.

Alternatively, you can install the "Shake" build system from
https://shakebuild.com. Then you will be able to use the Shakefile.hs
that I created. This gives the ability to do incremental builds, as
opposed to a full rebuild. This is only really necessary if you intend
to work on the compiler itself, however (the "gcc" command given above
probably works well enough for most users).

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



# Future directions

My main motivation for working on this project is that I would like to
explore whether it is feasible to use formally verified languages,
combined with modern SMT solver technology, to create "real" programs.
To this end I would like to start writing some larger projects in the
Babylon language -- perhaps a simple 2-D game (I am particularly
interested in the roguelike genre).

Rewriting the compiler in its own language could also be interesting,
although I don't think I have time for such a large project right now!
(Perhaps sometime in the future.)

As far as the language itself goes I have several ideas for things I
would like to add:

 - "Refs" could be improved. Currently it is possible to pass function
   parameters by reference, but not, for example, to return a
   reference, or store a reference in a data structure. Rust, with its
   "borrow checker", does allow such things, so perhaps we could
   consider implementing some similar ideas in Babylon.

 - It would be nice to support higher order functions (i.e. passing
   functions to other functions). The main barrier to this is that
   most SMT solvers do not support higher order functions, so it would
   be hard to translate higher order programs into something that an
   SMT solver could understand. However I think there are some things
   that could be done, so this would be worth investigating.

 - Haskell-like type classes could be interesting to add. With the
   verifier, we could not only state the list of operations that a
   type class should support, but also a set of axioms that must be
   satisfied by all instances.

 - Recursion is not currently supported, but should be added. (To ensure
   termination, we would require a "decreases" clause on any recursive
   function.)

 - Miscellaneous other language features should be added, e.g. "for"
   loops, "break" and "continue" in while loops. Infinite loops should
   be supported (not by default, but sometimes they are needed).
   Various other things.

 - I'm considering changing arrays so that they are represented just
   by a pointer, instead of a tuple of pointer and size (as they are
   currently). This would mean that "sizeof" would become a ghost
   construct. Programmers would still be able to pass the size around
   together with the array if they wanted to, but this change would
   optimise the case where you already know the size (or don't need
   it) and just want to pass the pointer around.

 - The interface for calling C from Babylon could be improved.
   Currently it is completely undocumented -- basically the programmer
   has to know the exact structure layout that the Babylon compiler
   uses, and then mimic that structure in the C code. (This is further
   complicated by the Babylon compiler's insistence on using packed
   structs everywhere -- that's something else that should be fixed, to
   be honest.) It would be better if we had some kind of formally
   defined "foreign function interface".

There are also improvements that could be made to the compiler:

 - The error messages need to be improved.

 - The provers to be used should be specified in some config file (or
   similar) rather than hard coded into the compiler.

 - The compiler needs to produce better code. We should either rewrite
   the code generator to be more like a conventional compiler backend
   (with separate instruction selection, register allocation,
   optimisation passes and so on); or else we could explore generating
   C code, and using a C compiler to do the hard work of optimisation.
   Alternatively we could use something like LLVM. There are lots of
   options here.

 - The compiler should be portable to other architectures and
   operating systems (currently it only supports x86-64 / Linux).

 - It might be useful to give more control over the verifier. E.g.
   systems like Isabelle have a "using" construct, which allows control
   over which facts/theorems are actually passed to the solver
   (sometimes passing a smaller, more relevant set of facts can make
   the problem easier to solve). It might be good to have something
   similar in Babylon.

In short, there is a long way to go before this becomes a truly
"useful" programming language, but what we have so far is a good start
and a good basis for future experimentation and development.


# Related projects

This whole project was very much inspired by
[Dafny](https://dafny.org/). However, Dafny is targetting managed
languages (for example, they use a garbage collector) whereas I am
more interested in the kind of lower-level programming that one might
do in Rust or C. (For example, I have explicitly-sized integers, like
"i32" or "u64", whereas Dafny uses an infinite-sized "int" type.) This
is why I mentioned Rust above -- perhaps combining some of Rust's
ideas with the verification features of Dafny could be an interesting
direction to go in.

There are also many other verifcation and proof systems out there,
including [Coq](https://coq.inria.fr/),
[Lean](https://lean-lang.org/), [Agda](https://github.com/agda/agda),
[Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/),
[Whiley](https://whiley.org/),
[Isabelle](https://isabelle.in.tum.de/), and so on. In fact too many
to list here.

One important distinction is that systems like Coq or Isabelle place a
great emphasis on really making sure that the proofs are correct and
trustworthy. On the other hand, systems like Babylon are willing to
trust the results of an SMT solver, without further checks being made.
This means that theoretically, a Babylon program could be successfully
verified, yet not be correct, due to a bug in the SMT solver. (Or
indeed a bug in the compiler itself!) Personally I am happy with this
trade-off, but for users who really require a cast-iron guarantee that
the verification is correct (for example in safety-critical systems?),
then Babylon would *not* be a good choice, and one of those other
systems would be better.


# Contact

I can be contacted by email at: stephen (at) solarflare.org.uk
