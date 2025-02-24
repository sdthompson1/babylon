This folder contains several examples of "packages" written in the
Babylon language.


# Useful Libraries

**coretypes** contains basic definitions that will be useful for many
programs, e.g. functions for working with arrays, strings and
integers, and "Maybe" and "Result" types. Most, if not all,
applications will want to include this.

**io** contains a simple file I/O library, and also a "Console" module
with some basic functions for printing to stdout.

**gfx-engine** contains a simple 2D graphics library, based on SDL.
This allows us to write programs that draw simple shapes and textures
on screen, and read mouse and keyboard input. It is used by the
"chess" demo (see below).

**datetime** is a simple date/time library. It is based on the
proleptic Gregorian calendar, without any support for time zones or
leap seconds. It also contains functions for reading the system clock
and sleeping for a given period of time.

**random** is a simple random number library. It includes a basic
random number generator as well as a function for getting a
non-deterministic "seed" value from the operating system.


# Demo Applications

**example01** through **example15** are a series of examples
explaining different features of the Babylon language. If these are
read in order, then the reader should get a reasonably good idea of
how the language and compiler work.

**chess** is a somewhat larger example implementing an interactive
chess game.


# See Also

See also the [docs](../docs) folder, which contains the documentation
for the Babylon language and its compiler.
