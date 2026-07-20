This directory contains Isabelle code for a (very early version of) a
verified Babylon compiler. Currently it implements the compiler "front
end" (lexer, parser, module loader and renamer) together with an
elaborator which converts the input program into a typechecked "Core"
language.

To build this, you can use the following Isabelle command:

```
isabelle export -d. -x Babylon.CodeExport:code/** Babylon
```

(Note: the `isabelle` executable can be found in the `bin` directory
of your [Isabelle](https://isabelle.in.tum.de/) distribution. At the
time of writing I am using Isabelle 2025 for Linux.)

The above `isabelle` command will create Haskell code in
`export/Babylon.CodeExport/code/export1/`. You can then copy (or
symlink) the provided `Main.hs` into that directory, then `cd` to that
directory and run

```
ghc -O Main.hs
```

This will create an executable named `Main`, which can be run as
follows:

```
./Main Foo.b Bar.b ...
```

Each filename given on the command line is read as the source code of
one Babylon module. The first module on the command line is the root
module for the compilation. Each module's name (in the source text)
must correspond to the filename, e.g. `dir/Foo.b` must is the module
`Foo`.

The program runs the front end and elaborator on the given modules. If
everything succeeds it prints `Success`; otherwise the error messages
are printed to stderr and the exit code is nonzero.
