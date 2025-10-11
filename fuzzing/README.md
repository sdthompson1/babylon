# Fuzz Testing the Babylon Compiler

This document describes how to use fuzz testing (with
[AFL++](https://github.com/AFLplusplus/AFLplusplus)) to look for bugs
in the Babylon compiler.

# How it works

This section describes the theory behind our fuzz testing approach.
(If you just want instructions on how to run the fuzz testing, skip to
the next section.)

We now, effectively, have two Babylon compilers:

1. The main Babylon compiler written in C (`bab` command)
2. A new implementation being done in Isabelle (currently only
   partially implemented)

This gives an obvious testing opportunity: we can run both of the
compilers on lots of different inputs, and confirm that they both
"agree" on the result in each case. If not, then a bug in one or other
of the compilers has been found.

To develop this idea further, we can define the "result" of a
compilation to be one of the following status codes:

| Status Code | Meaning |
| --- | --- |
| 0 | Success |
| 1 | Error at lexer stage |
| 2 | Error at parser stage |
| 3 | Error at renamer stage |
| 4 | Type error |
| 5 | Verifier error |
| 6 | C compiler or linker error |

A `bab fuzz` subcommand has been implemented (in the C Babylon
compiler) which does roughly the following:

1. Compile the program as normal (using the C implementation) but stop
   after typechecking. Extract the "status code" (either 0, 1, 2, 3 or
   4) from the compilation process.

2. Also call the Isabelle implementation of the compiler, returning
   another "status code".

3. If the two status codes are equal, exit the `bab fuzz` command
   normally; otherwise, call `abort()`.

(There is also an option to ignore status codes greater than a certain
value. This is currently needed because the Isabelle compiler doesn't
implement all the stages of the compiler yet; hopefully that will be
fixed in the reasonably near future.)

We then use AFL++ to repeatedly run this `bab fuzz` command with a
large number of randomly generated inputs. Any mismatches between the
two implementations would be detected as crashes by AFL++ (because
they would result in calls to `abort()`).

Any crashes found can then be followed up by adjusting the C or
Isabelle implementation (or both) to make them give consistent results
when presented with that input.


# Instructions for running `bab fuzz` with AFL++

This section gives instructions on how to use the `bab fuzz` command,
in conjunction with AFL++, to implement the fuzz testing process
described above.

First, build the Isabelle and Haskell code as described in [the README
in the isabelle folder](../isabelle/README.md). This should create an
executable called `Main`.

Also, install [AFL++](https://github.com/AFLplusplus/AFLplusplus) if
you haven't already.

Now, build the `bab` command with AFL instrumentation, using the
following commands (from the root of the Babylon repository):

```
make clean
make CC=afl-cc
```

(Note: This builds the instrumented binary in the same `build`
directory as the normal `bab` build. It is therefore important to run
`make clean` after you are done fuzzing, so that you don't get the
instrumented object and binary files mixed up with the regular ones.)

Now, you can start fuzzing with the following command. Run this from
the repository root:

```
afl-fuzz -x fuzzing/dictionary -i fuzzing/seeds/ -o afl-output/ -- ./build/bab fuzz -r fuzzing/dummy-package --main-file @@ --oracle isabelle/export/Babylon.CodeExport/code/export1/Main --max-status 3
```

This will create an `afl-output` folder. Any crashes found will be
stored in `afl-output/default/crashes`.

Some notes:

 - `-x fuzzing/dictionary` tells AFL++ to use the given "dictionary"
   file. Currently this just contains a list of valid Babylon tokens
   (keywords, punctuation symbols and so on). The hope is that AFL++
   would be able to use this to generate better input examples than it
   would be able to by pure bit flipping alone.

 - `-r fuzzing/dummy-package` gives the path to the Babylon package
   that we will try to compile (with both compilers). This is
   basically just an empty shell containing an empty `Main.b` file,
   but it needs to be present otherwise the `bab` compiler would not
   be able to work properly.

 - `--main-file @@` tells the compiler to override the contents of
   `Main.b` with the random data coming from the fuzzer. This is how
   the random input data is transmitted into the compiler.

 - `--oracle isabelle/export/Babylon.CodeExport/code/export1/Main`
   gives the path to the "oracle" executable (the Isabelle compiler).
   This currently receives the source code filename as a command line
   argument, and passes the corresponding result code back to `bab`
   via its exit status.

 - `--max-status 3` says that the maximum exit status value that can
   be returned from the oracle is 3. As the Isabelle compiler is
   extended in future, we will be able to use higher `--max-status`
   values.


# Future directions

At the moment, the lexer and parser have been fuzz tested reasonably
thoroughly, meaning that the C and Isabelle implementations of these
stages should give fairly consistent results. The logical next step is
to implement further compiler stages on the Isabelle side (up to and
including typechecking) and carry out further fuzz testing to ensure
that these are consistent with the C implementation.

After that, the plan would be to fill out the rest of the Isabelle
implementation, including compiler and verifier stages (similar to
`bab compile` and `bab verify`), as well as a simple "interpreter"
(which could act as a formal definition of the intended semantics for
the language). Ideally proofs of certain properties (such as type
safety properties) would be done at the same time. This is obviously a
longer-term project.

A further step could be to write a tool, similar to
[Csmith](https://github.com/csmith-project/csmith), which is able to
generate random valid Babylon programs. We could then use this tool to
generate a large number of random programs and check that those
programs give the same output when run via the `bab compile` tool, the
Isabelle Babylon interpreter, or the Isabelle Babylon-to-C translator.
This would complement the AFL++ testing nicely and would provide a
good check that the `bab` compiler is indeed giving the same results
as the more formal Isabelle implementation.
