This directory contains Isabelle code for a (very early version of) a
verified Babylon compiler. For now, it only implements a lexer and
(some of) a parser, nothing else.

The main use of this is for fuzz testing: see
[fuzzing/README.md](../fuzzing/README.md) for details.

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

This will create an executable named `Main`, suitable for use as an
"oracle" with the `bab fuzz` command (see the [fuzzing
README](../fuzzing/README.md) for details).
