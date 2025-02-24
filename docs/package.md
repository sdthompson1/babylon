
# Babylon Package System

Stephen Thompson, February 2025

This file describes the "package system" currently used by the Babylon
programming language.


# Introduction

The [Babylon language reference manual](lang-ref.md) defines a Babylon
program as a collection of Babylon modules, perhaps together with some
`extern` functions (that is, functions written in a different
programming language -- usually C). In other words, a complete Babylon
program consists of a set of `*.b` files, possibly augmented with
`*.c` and `*.h` files (if external C code is needed).

However, the language reference manual does not say anything about how
these files are to be organised on disk. The simplest approach would
just be to dump all the files into a single directory and then point
the compiler at that directory. However, we would prefer something a
little more "structured" than that. For example, what if one
programmer wants to write a library of useful functions, and another
developer wants to write an application using that library? Or what if
there are several libraries involved? With the "dump all files in one
directory" approach, we would have to mix all the files from the
different developers together into one disk folder; development would
quickly become chaotic and disorganised.

The purpose of the package system, therefore, is to support this
"library" use case by allowing a group of related `*.b`, `*.c` and
`*.h` files (along with any metadata required) to be distributed
together as a single "package". Each library can then become a package
in its own right; the application that uses the libraries is also a
package. Packages support the concept of dependencies, so an
application package will depend on its library packages, and library
packages may depend on other libraries.

With this system in place, we can store each package on disk in its
own directory. Then, to run a build, we can just tell the compiler the
location of a "root" package, along with a "search path" for finding
dependencies; the compiler then does the rest, figuring out which
files it needs to include in the build simply by following the
dependencies, starting from the root package.


# Definition of a package

A Babylon package, by definition, is a directory on disk containing
(at least) the following elements:

 - A `package.toml` file, containing metadata such as the name and
   version of the package, and the names and minimum versions of any
   dependencies.

 - A `src` directory, containing the `*.b` files corresponding to this
   package's Babylon modules, plus (optionally) any `*.c` or `*.h`
   files required.

Note that the directory name used should either be the same as the
package name, or it should be the package name followed by a hyphen
followed by the package version. For example, if we have a package
whose name and version (according to its `package.toml`) are `foo` and
`0.1` respectively, then the package directory should be named either
`foo` or `foo-0.1`. (Following this convention is necessary to ensure
that the compiler is able to locate package directories on its search
path when required; see also "Compilation" below.)


# Format of the `package.toml` file

As mentioned above, all Babylon packages contain a `package.toml` file
in their top-level directory. This is a [TOML](https://toml.io/en/)
file containing metadata about the package.

Here is an example `package.toml` file, illustrating the general
structure:

```
[package]
name = "example-package"
description = "An example to illustrate the package.toml file format"
version = "2.6"

[modules]
main-module = "Main"
main-function = "main"
exported-modules = ["Module1", "Module2"]

[dependencies]
events = "1.3"
calendar = "2.4"
user-interface = "3.1"

[system-packages]
gmp = "6.2.1"
libpng = "1.6.37"
math = ""
```

We now describe each of the sections in this file in more detail.


## `package` section

This contains basic information about the package.

 - `name` gives the name of the package. Currently, package names must
   be non-empty and consist only of alphanumeric characters,
   underscores and hyphens.

 - `description` gives a short description of the package. This string
   is ignored by the compiler, but can be useful to human readers of
   the `package.toml` file.

 - `version` gives the version number of the package. This should
   usually be in the Semantic Versioning format, but compliance with
   this is not strictly enforced.


## `modules` section

This defines the "main module", "main function" and "exported modules"
for the package. See "Compilation" below for details of what these
actually mean for the build.

 - `main-module` gives the name of the "main module" for this package,
   if there is one.

 - `main-function` gives the name of the "main function". If this is
   set, then a function with this must exist in the interface of the
   `main-module` and it must take no arguments and return no value.

 - `exported-modules` gives the list of "exported modules" for this
   package.

Note that at least one of `main-module` or `exported-modules` must be
present in any package.


## `dependencies` section

Each item in this section is a key/value pair, where the key is the
name of another package, which this package depends upon, and the
value is a string, giving the minimum acceptable version of the
dependency.

See "Dependencies and Versioning" below for details of how the
dependencies are searched for on disk, and what the version numbers
mean.


## `system-packages` section

This section allows us to develop packages that call "system
libraries", such as libgmp, SDL, or any other libraries that happen to
be available on the target platform.

For the time being, "system packages" are defined as anything that can
be accessed through the `pkg-config` command.

In particular, if `name = "version"` is included as one of the
key/value pairs in the `system-packages` section, then the output of
`pkg-config --cflags name >= version` will be included as part of the
C compiler command line, and `pkg-config --libs name >= version` will
be included as part of any linker command line used.

Note that if the `pkg-config` command fails (e.g. because the
requested package is not available on the system or its version is not
high enough) then compilation will be aborted instead.

The system package named `math` is a special case. For this system
package, `pkg-config` is not run, and instead `-lm` is added to the
linker command line (and nothing is added to the C compiler command
line). This allows packages to call functions from the math library
(such as `sin` and `cos`) from their C code, if desired.


# Dependencies and Versioning

As noted, packages can depend on other packages. For each dependency,
the `package.toml` file specifies the *minimum* version of the
dependency that this package can accept.

Note that only one version of any particular package can occur in any
given build. If two packages each depend on a third package named
`foo`, but one requires version X and the other version Y, then the
version used will be whichever is the *greater* of X or Y, because
this is the minimum version of the dependency that will satisfy both
requirements. (This is similar to Go's so-called "Minimal Version
Selection" algorithm.)

Version strings are compared using the following algorithm: First,
each string is split at `.` characters, resulting in a tuple of
substrings. Secondly, the resulting tuples are compared
lexicographically; and when comparing tuple components, if both
strings purely consist of the digits 0 to 9, then they are compared as
integers, otherwise they are compared as strings.

For example:

 - `0.12.2` is considered a higher version than `0.3.7`, because the
   first components of each version (`0` and `0`) are equal, and the
   second components (`12` and `3`) are to be compared numerically,
   with 12 being greater than 3.

 - `0.12a.2` is considered a lower version than `0.3.7`, because this
   time the second version components (`12a` and `3`) do not both
   contain only digits (one contains an `a`), so they are compared as
   strings, and therefore, `12a` is considered less than `3`.

 - `1.2a` is considered a lower version than `1.2a.b`, because the
   first two version components are common to both strings, but the
   second string has a third component, which is missing from the
   first string.

Once the compiler has determined that a package named N, of version V,
is required, then the compiler will begin searching for that package
on disk. Each folder on the compiler's "package search path" is
considered in turn. If the folder contains a subfolder named either
"N" or "N-V" (with N and V as above), and if that subfolder itself
contains a `package.toml` file with the correct `name` and `version`
values within, then the dependency is considered to have been found.
Otherwise, the compiler continues with the next folder on the search
path (or gives up, if the end of the search path has been reached).

For example, if we need to load version `0.1` of a package named
`foo`, then the compiler checks the first directory on its package
search path to see if it contains a subfolder named `foo`. If found,
it also checks that the `foo` subfolder contains a `package.toml`
file, and that the `package.toml` contains both `name = "foo"` and
`version = "0.1"` in its `[package]` section. If all these conditions
are met, we are done. Otherwise, the compiler checks again, but this
time it looks for a subfolder named `foo-0.1` instead of just `foo`.
If the package is still not found, then the compiler repeats the whole
process with the second folder in the search path, and then the third,
and so on, until either a match is found, or the compiler gives up and
reports the dependency as "not found".

This system means that users can choose, if they wish, to keep several
different versions of a package on disk (as long as they use the
correct version suffixes on the directory names, as described above).
Alternatively, users may choose to keep only one version of the
package (the one they are actually using), in which case they don't
need to bother including the version number suffix in the directory
name -- although the correct version string still needs to be listed
in the `package.toml` file under the `version` key.


# Compilation

Before any `compile` or `verify` job can run, we need to determine the
set of files that are to be considered as part of the build.

The rules for doing this are as follows:

 1. If the *root* package for the build defines a `main-module`, then
    the `*.b` file corresponding to that module is included in the
    build. Similarly, if the *root* package defines any
    `exported-modules`, then the `*.b` files corresponding to those
    exported modules are included in the build.

     - To find out the name of the `*.b` file corresponding to any
       given Babylon module, we simply take the module's name, convert
       any dots to slashes, and then add `.b`. This file is then
       searched for in the `src/` subfolder of the package. For
       example, a module named `Foo` would correspond to a file named
       `src/Foo.b`, and a module named `Foo.Bar.Baz` would be found in
       `src/Foo/Bar/Baz.b`.

     - A consequence of the above is that "dotted" module names
       correspond to subdirectories within the `src` folder. This can
       be a useful feature, especially for larger packages, as it
       means that module files can be organised into some kind of
       logical hierarchical structure on disk, if desired.

 2. If any `*.b` file included in the build contains an `import`
    directive, then the `*.b` file for the module being imported is
    also included in the build. (This continues recursively until all
    "imported" `*.b` files have been included in the build.)

     - Imports are always searched for in the current package first.
       For example, if `import Foo.Bar;` is encountered, and there is
       a file `src/Foo/Bar.b` in the current package, then that is the
       file that is being imported.

     - If an import is not found in the current package, then it is
       searched for in the dependency packages. Only modules
       explicitly exported from the dependencies (via
       `exported-modules` in the `package.toml` file) will be
       considered in this case.

        - Note that if the same module name is exported by two or more
          dependencies, then this is an error. (However, if the same
          module is both present in the current package, and exported
          by some dependency package, then this is not an error; the
          module from the current package "shadows" the dependency in
          that case.)

 3. If any `*.b` file is included in the build, and a corresponding
    `*.c` file is present in the same directory as the `*.b` file,
    then that `*.c` file is also included in the build. (For example,
    if `src/Foo.b` from some package is included in the build, and
    `src/Foo.c` exists in that same package, then `src/Foo.c` will
    also be included in the build.)

Some notes:

 - If a package *other* than the root package contains a `main-module`
   or some `exported-modules`, then those modules are not
   *automatically* included in the build; they only get included if
   something from the root package (directly or indirectly) imports
   them. (In other words, if you are developing a package and you
   specify a dependency on some library package, then you will not
   necessarily have to compile or verify the entire library; only the
   modules that you are actually using will be compiled or verified.)

 - If there are `*.c` files in the `src` folder then these do not all
   automatically get compiled as part of the build. Only `.c` files
   whose names correspond to an included `.b` file will actually be
   compiled and linked. For example, if `Foo.b` contains a Babylon
   module, then `Foo.c` would typically contain the C code for any
   `extern` functions declared by that module. If module `Foo` ends up
   not being included in the build (because nothing imports it) then
   the corresponding C functions also won't be compiled and linked.

    - This is usually what we want. However, there may be cases
      where we need more than one C file to define all of the `extern`
      functions provided by a module. For example, perhaps module
      `Foo` declares so many `extern` functions that the
      implementation needs to be split into `Foo1.c`, `Foo2.c` and
      `Foo3.c`. In cases like this, it is usually possible to find
      some workaround involving `#include` directives. For example,
      one could write a short `Foo.c` file which simply includes
      `Foo1.c`, `Foo2.c` and `Foo3.c` one after the other.

 - Note that when importing modules with "dotted" names, the imported
   module must always be referred to by its full name, not an
   abbreviation. For example, to import the file `src/Foo/Bar/Baz.b`,
   you must always write `import Foo.Bar.Baz`, not `import Baz` or
   anything similar (even if the "importing" module is already itself
   in the `src/Foo/Bar/` directory). In other words, unlike in some
   languages (like Python), "relative" imports (in the sense of being
   relative to the current source file's directory) are not supported
   in Babylon.


# Use Case Examples

Here are some examples of how different kinds of packages might be
set up:

 - For a library package, we would typically define `exported-modules`
   but not a `main-module`.

    - In this case, running `bab verify` on the package would verify
      all of the exported modules (plus their imports), which is what
      we want in order to make sure that the library is successfully
      usable by another package.

    - Running `bab compile` on the library package won't do anything
      useful (because there is no "main" function defined), but this
      is fair enough, since a library cannot be compiled to an
      executable (on its own) anyway.

 - Another way to set up a library package might be to include a
   `main-module` and `main-function` that runs some kind of automated
   unit tests. (This would be in addition to the `exported-modules`
   list.)

    - In this case, running `bab compile` on the library package will
      now create an executable; running this executable will perform
      all the unit tests for the library.

    - Any package that depends on the library will *not* have to build
      the unit tests, because of the rule that the `main-module` of a
      dependency package is not automatically included in the build.
      This means that any "testing" code is not linked into
      applications which use the library, which is usually what we
      want.

 - For an "application" package (i.e. a top level package) we would
   usually want to include both a `main-module` and a `main-function`.
   Typically an application would also depend on several library
   packages (which might themselves have dependencies).

    - Running `bab verify` on the package will verify both the
      application code itself, plus the library packages -- or at
      least, any modules from the libraries that are actually used.
      (Unused parts of the libraries will remain unverified, which is
      usually what we want, because it saves time and the unused parts
      cannot affect the final executable anyway.)

    - Running `bab compile` will build the application code together
      with any code from the libraries that the application needs.
      Executing the application will start from the `main-function`,
      as expected.

    - An alternative way to set it up would be to write the "main"
      function in C instead of Babylon. In other words, we can have a
      C application which calls some Babylon functions from time to
      time, instead of the other way around. To set this up, we can
      define a `main-module` (let's call it `Main.b`) but leave
      `main-function` undefined. We would then arrange for `Main.b` to
      import any Babylon modules that the C code will require.
      Finally, we implement a `Main.c` file which contains the C
      `main` function. This `main` function can then call any Babylon
      (or C) functions that are part of the build (i.e. directly or
      indirectly reachable from `Main.b` according to the above
      rules).

For some more concrete examples, see the `packages` folder that is
shipped as part of the Babylon compiler. This contains several
standalone programs (such as `chess`, a chess game) as well as some
examples of library packages (e.g. `coretypes`, `io`, `datetime` and
`gfx-engine`).



# Future Work

Currently, if a user (hypothetically) wanted to download and use a
Babylon package found from some online source, that user would first
have to download the package to their local computer, then unpack its
contents to a directory (with the correct name), then arrange for that
directory to appear on the Babylon compiler's search path. This is all
a little bit inconvenient.

One possible improvement might be to allow Git URLs to be used (in the
`babylon.toml` file) when specifying the package dependencies. If this
was done, the compiler would invoke an external `git` command to
download the package to some local "cache" directory, and then
automatically use the local copy in the build. This would save the
user some manual work in downloading the packages and setting things
up locally.

A "fancier" alternative might be to set up a central package
repository, similar to https://crates.io/ for Rust for example. This
would be even simpler to use, as users would just have to give the
package name and (optionally) a minimal version, and the compiler
would automatically locate and download the package. It would also
give a central place where users could look for and share Babylon
code. This might be something to consider if the Babylon language
becomes more widely used in the future.
