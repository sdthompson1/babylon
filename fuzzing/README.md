# Fuzz Testing the Babylon Compiler

This section describes how we can use fuzz testing (with
[AFL++](https://github.com/AFLplusplus/AFLplusplus)) to look for bugs
in the Babylon compiler.

# Theory of operation

We now effectively have two Babylon compilers (although only one is
even remotely complete/working yet):

1. The main Babylon compiler written in C (`bab` command)
2. A new implementation being done in Isabelle (currently only
   implements the lexer and some of the parser)

Having two different compiler implementations provides a powerful way
to check for bugs. We can simply run both compilers (for a given
input) and check that they give the same result. The idea is that if
we have two independently developed implementations of a compiler, and
they both give the same results for a wide range of inputs, then we
can have a high degree of confidence that both implementations are
correct. Conversely, if an input file is discovered which causes the
two implementations to give different results, then we know one or
other of the implementations must have a bug.

To develop this idea further, we can define the "result" of a
compilation run to be one of the following status codes:

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

2. Call an external "oracle" program, passing the source code. The
   oracle also returns a numeric status code.

3. If the two status codes are equal, exit the `bab fuzz` command
   normally; otherwise, call `abort()`.

The "oracle" program is simply the Isabelle implementation of the
compiler (with a small Haskell `Main.hs` program to act as a driver).
This program currently just reads the source code, lexes it, and
returns either status 0 (no errors) or status 1 (lexical error
detected). (In future, it will also parse, rename and typecheck,
allowing it to return status codes 2, 3 or 4 as well.)

The idea is that `bab fuzz` will crash (call `abort()`) if it finds
any difference between its own compilation result and the result given
by the "oracle" (i.e. the Isabelle implementation).

We then use AFL++ to repeatedly run this `bab fuzz` command with a
large number of randomly generated inputs. Any problems found would be
detected as crashes by AFL++.

It seems to me that if any bugs in the lexer or parser stages exist,
then the above process would likely be able to find them sooner or
later. The renamer and typechecker stages are more debatable, but it
is certainly possible that bugs with those stages might be found this
way as well (especially if a diverse range of input seeds is provided
to AFL++). Unfortunately, I doubt that bugs in the verification or C
code generation stages could be found this way, as it seems unlikely
that a valid Babylon program, long enough to exhibit (say) a code
generator bug, could be created simply by a random bit flipping
process. Therefore, another method would probably be needed to find
bugs in the later compiler phases (corresponding to status codes 5 and
6, let's say). To deal with this, I have another plan involving
writing a custom tool to generate valid Babylon programs at random --
see the "Future directions" section below for further discussion.

For now, we will focus on using AFL++ to find bugs in the earlier
stages of the compiler.


# Instructions for running `bab fuzz` with AFL++

This section provides practical instructions on how to implement the
process described above (i.e. running the `bab fuzz` command under
AFL++).

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

(Note: After you are done fuzzing, don't forget to run `make clean`
again, to get rid of the AFL-instrumented object files and
executables!)

Now, you can start fuzzing with the following command. Run this from
the repository root, replacing `/path/to/Main` with the appropriate
path to the `Main` executable (which we created earlier):

```
afl-fuzz -x fuzzing/dictionary -i fuzzing/seeds/ -o afl-output/ -- ./build/bab fuzz -r fuzzing/dummy-package --main-file @@ --oracle /path/to/Main --max-status 1
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

 - `--oracle /path/to/Main` gives the path to the "oracle" executable
   (the Isabelle compiler). This currently receives the source code
   filename as a command line argument, and passes the corresponding
   result code (currently either 0 or 1) back to `bab` via its exit
   status.

 - `--max-status 1` says that the maximum exit status value that can
   be returned from the oracle is 1. Effectively, this means that the
   oracle only implements the lexer stage of the compiler currently.
   So if the `bab` command finds, say, a parser error (status code 2),
   it will ignore this and expect the oracle to return status 0 in
   this case. (As the Isabelle implementation is extended in the
   future, we will be able to use higher `--max-status` values.)


# Future directions

The fuzzing currently runs very slowly. This could be improved quite
easily by implementing AFL's "persistent mode". The interface between
`bab fuzz` and the oracle process could also be improved. Currently a
new oracle process needs to be forked for each new compiler run.
Instead, we could implement a procedure whereby the `bab` command
sends a compile job to the oracle via its stdin, and receives the
result back via the oracle's stdout. This would allow re-using the
same oracle process for multiple compilation jobs, which should speed
things up a great deal.

After that is done, the Isabelle compiler implementation needs to be
filled out a lot more. The parser, renamer and typechecking stages
should be implemented. We could then fuzz test all status codes from 0
to 4 inclusive using the above process (for this, the `fuzzing/seeds`
folder should be filled out some more, with as many examples of valid
Babylon programs as possible, ideally).

Going beyond that, I intend (eventually) to implement both an
interpreter for the Babylon language, and a "translator" from Babylon
to C code, in the Isabelle code. Ideally, a proof would also be done
(in Isabelle) that the translated C code has the same semantics as the
interpreter.

A further step could be to write a tool, similar to
[Csmith](https://github.com/csmith-project/csmith), which is able to
generate random valid Babylon programs. We could then use this tool to
generate a large number of random programs and check that those
programs give the same output when run via either the `bab` compiler
tool, or the Isabelle Babylon interpreter. This would complement the
AFL++ testing nicely and would provide a good check that the `bab`
compiler is indeed giving the same results as the more formal Isabelle
implementation.
