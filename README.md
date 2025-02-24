
# The "Babylon" programming language

[Babylon](https://www.solarflare.org.uk/babylon) is a new programming
language designed to support formal verification within the context of
a low-level, C- or Rust-like language.

Design goals:

 - Support for formal verification (e.g. preconditions,
   postconditions).
 - Well-defined semantics (no "undefined behaviour" like C).
 - Keep it simple (no overly complex language features).
 - Minimal runtime system requirements (e.g. no garbage collection).
 - Interoperability with other languages such as C.

Current status:

 - Version 0.1 of the compiler (supporting both compilation and
   verification of Babylon programs), along with
   [documentation](docs), is now available.

    - Compilation is done by translating the Babylon program to C,
      then using an external C compiler to produce an executable.

    - Verification is done using external [SMT
      solvers](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories).
      Any solver supporting the SMT-LIB interface can be used; I have
      personally had good results with
      [z3](https://github.com/Z3Prover/z3),
      [cvc5](https://cvc5.github.io/) and
      [vampire](https://vprover.github.io/).

 - The compiler is now reasonably complete, and working well; it is
   possible to write and verify medium-sized programs using it. Having
   said that, it is still only a prototype, so while people are
   welcome to "try out" the language, it might be advisable to wait
   for a later version (e.g. 1.0) before embarking upon any serious
   projects using it.

Future goals include:

 - New language features (currently some important features are
   missing, e.g. recursion).
 - Self-hosted compiler implementation (currently the compiler is
   written in C).
 - Resource consumption limits (e.g. being able to prove bounds on
   memory allocation or number of CPU operations carried out by a
   program).
 - Formal rigorous definition of the language (e.g. using Isabelle
   or Coq).
 - Miscellaneous other improvements.


# Examples

Here is a simple example Babylon program:

    module Prime

    interface {
        // Define what is meant by a prime number.
        ghost function is_prime(n: i32): bool
        {
            return n >= 2 &&
                forall (i: i32) 2 <= i < n ==> n % i != 0;
        }

        // Declare an executable function which will check whether a
        // given number is prime.
        // Note the "ensures" condition which means that the compiler
        // will verify that the function meets its specification, i.e.,
        // it returns true if and only if `is_prime(n)` is true.
        function check_if_prime(n: i32): bool
            ensures return <==> is_prime(n);
    }

    // This is the implementation of "check_is_prime".
    // (This is not the fastest way to detect prime numbers by
    // any means, but it is simple and easy to verify.)
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

Further examples can be found in the [packages](packages) folder of
this repository. Some highlights:

 - [Demo_07_Primes.b](packages/Demo_07_Primes.b) is a more efficient
   prime number calculator using the Sieve of Eratosthenes.

 - [Demo_14_GCD.b](packages/Demo_14_GCD.b) implements Euclid's
   algorithm for finding the greatest common divisor of two numbers.

 - [chess](packages/chess) implements a simple interactive chess game.
   This uses [SDL](https://www.libsdl.org/) to do the graphics and
   mouse input.

![](examples/chess/screenshot.png)

*A screenshot of the chess demo. The Babylon compiler verifies that
this program cannot crash at runtime (or at least, the parts written
in Babylon cannot crash -- the program does also include C code which
is unverified). We do not verify functional correctness, i.e. that the
rules of chess are correctly implemented -- but perhaps that could be
a future project!*


# Building/Installing

This section describes how to build the Babylon compiler.

A Linux machine, with the `gcc` and `make` commands and the
`libsqlite3` library, is required.

To build the compiler you can simply run "make". An executable file
`build/bab` will appear.

If you want to use the verifier, you will need to make sure that at
least one (and preferably at least 2--3) of the commands `z3`, `cvc5`,
`vampire` or `alt-ergo` are available on your system. (I personally
use the first three from that list.) You might be able to get
pre-built binaries at the following links:
[z3](https://github.com/Z3Prover/z3/releases),
[cvc5](https://cvc5.github.io/downloads.html),
[vampire](https://github.com/vprover/vampire/releases),
[alt-ergo](https://alt-ergo.ocamlpro.com/). Otherwise they can be
built from source. Put the binaries into your search path somewhere.

The first time the `bab` command is run, it will scan the `PATH` to
see which SMT solvers are installed, and create an appropriate config
file in `$HOME/.config/babylon/babylon.toml`. Therefore, install any
required SMT solvers before running `bab` for the first time. You can
also edit the config file manually, and/or run `bab check-config` to
verify that the config is correct.

You can also run `make check` to run a suite of compiler self-tests,
if you wish.

For instructions on how to use the compiler, check the [docs](docs)
folder, and/or look at the `example` directories under
[packages](packages) (reading these in numerical order will provide a
tutorial of sorts).


# Further Info

There is a [project website](https://www.solarflare.org.uk/babylon)
containing some additional info about the project.


# Disclaimer

For the avoidance of doubt: this project is currently considered an
experimental prototype, not a fully working system, and is provided
WITHOUT WARRANTY OF ANY KIND.


# Contact

I can be contacted by email at: stephen (at) solarflare.org.uk.
