
# Babylon v0.1 Compiler Manual

Stephen Thompson, January 2025

This is a description of version 0.1 of the `bab` command line
program, which is a (prototype) compiler and verifier for the Babylon
programming language.


# Synopsis

```
bab compile [-r <path>] [-p <path>] [-o <path>] [-v] [-d]

bab verify [-r <path>] [-p <path>] [-o <path>]
           [-m <module-name>] [-q] [--continue] [-t <seconds>]
           [--no-cache] [-d]

bab build [-r <path>] [-p <path>] [-o <path>] [-v] [-q]
          [--continue] [-t <seconds>] [--no-cache] [-d]

bab translate [-r <path>] [-p <path>] [-o <path>] [-d]

bab check-config

bab version

bab help
```


# Description

The `bab` command has several available "subcommands", as follows:

 - `compile`: Compiles a Babylon program, producing an exectuable file
   as output. (Currently, this is done by translating the Babylon
   program to C code, then invoking a C compiler.)

 - `verify`: Verifies a Babylon program (or individual module) to make
   sure that it complies with all necessary conditions and
   requirements (for example, making sure that function pre and post
   conditions are satisfied, and that certain kinds of runtime errors
   do not occur). This relies on external SMT solver tools to do the
   required proofs.

 - `build`: This is a combination of `verify` and `compile`. It first
   verifies the program, and then, assuming verification passes,
   produces an executable.

 - `translate`: This is like `compile` except that it stops after
   producing the C code. In other words, it translates the Babylon
   program to C, but does not invoke the C compiler and does not
   produce an executable.

 - `check-config`: This runs various checks to make sure the `bab`
   program's own config file (`babylon.toml`) is correct.

 - `version`: Displays the version number of the `bab` program.

 - `help`: Displays help for the `bab` command or one of its
   subcommands (equivalent to `--help`).

The term "Babylon program", as used above, deserves some further
explanation. In general, a user of the `bab` command will specify a
path to a Babylon "package" as part of the command line. (Packages are
described in the separate "Babylon Package System" document, but in
general, a package can be thought of as a collection of related
Babylon modules, together with some metadata. Packages can depend on
other packages.) The package specified on the command line in this way
is known as the "root" package. The "Babylon program", then, really
just refers to the set of Babylon modules from the root package,
together with all Babylon modules from any packages that are (direct
or indirect) dependencies of the root. (In a complete program, one of
those modules will include a "main function", which then becomes the
entry point for the final compiled executable.)

In order to find the "dependency" packages, the compiler has the
concept of a "package search path", which is simply a list of
directories in which it will look to find any dependency packages that
are required. (Note that in future, it is possible that dependencies
might be automatically downloaded from the Internet, similar to Rust's
`cargo`, or Haskell's `cabal`, for example; but for now, any
dependencies required must be manually downloaded and placed into a
known location so that the compiler can find them.)

Any output files produced by the compiler (such as the generated
executable itself, any compiler intermediate files, or the
`babylon.cache` file created by the verifier) will, by default, be
placed in a `build` subdirectory of the chosen "root" package
directory (although the output directory can be overridden on the
command line if desired).

The compiler also relies on a separate config file, named
`babylon.toml`, usually located in `$HOME/.config/babylon/`, to
specify certain settings. At startup, if the `bab` program finds that
this config file doesn't already exist, then it will scan the system
`PATH` to find any working SMT solver programs (currently `z3`,
`cvc4`, `cvc5`, `vampire` and `alt-ergo` are supported) and then it
will automatically create a default `babylon.toml` file containing
details of any such solvers found. This process should work well for
most users; the key thing is to make sure that you have installed all
of the SMT solvers you want to use before running the `bab` command
for the first time. (If in doubt, run `bab check-config` to perform
some sanity checks on the config file, and/or inspect the file
manually to make sure it makes sense for your system.)


# Options

Not all options apply to all subcommands; see "Synopsis" above to see
which options are valid with which subcommands.

 - `-r PATH` or `--root PATH` specifies that the root Babylon package
   for the compilation should be searched for in folder PATH. (See
   also the discussion of "Babylon program" above.) This PATH should
   point to the folder that contains the `babylon.toml` file; it is
   specified relative to the current directory. A root package is
   required for all compile, build, translate or verify jobs; if no
   `-r` option is specified then the default of `.` (the current
   directory) is used. At most one `-r` option may be given.

 - `-p PATH` or `--package-path PATH` specifies that PATH should be
   added to the search path for "dependency" packages. For example, if
   it is determined that the program depends on a package named `foo`
   at version `0.3`, then the system will look in either
   `PATH/foo-0.3/package.toml` or `PATH/foo/package.toml` to find the
   corresponding `package.toml` file for the `foo` package (where
   `PATH` is the path specified in the `-p` option). Note that more
   than one `-p` option may be given; in this case, the paths are
   searched in the order they occur on the command line (from left to
   right).

 - `-o PATH` or `--output-path PATH` specifies that output files
   should be written to PATH. This defaults to `<root>/build` where
   `<root>` is the "root path" (as set in the `-r` option). If this
   folder does not exist then it will be created automatically.

 - `-v` or `--verbose` (when used with `compile` or `build`) prints
   out the compiler and linker commands (to stdout) as they are
   executed.

 - `-d` or `--debug` creates debug output files (in subfolders of
   `build`, or whatever output folder was specified instead in a `-o`
   option). The folder `build/debug_typecheck` will contain
   post-typechecking versions of the input Babylon modules, and will
   most likely be of interest to compiler developers only. The folder
   `build/debug_verify` contains internal versions of the SMT problems
   (`*.fol` files) as well as the actual SMT-LIB files as passed
   directly to the SMT solvers (`*.smt` files). The latter might be of
   interest to users in case they want to debug why their SMT problems
   are failing, although beware that the files can sometimes be quite
   long and difficult to understand!

 - `-m MODULE` or `--module MODULE` (when used with `verify`) means
   that the verification should be restricted to the module named
   MODULE only. This can sometimes be useful if one wishes to
   concentrate on verifying one particular part of the program "first"
   before moving on to other modules later.

 - `-q` or `--quiet` means that the "progress" messages from the
   verifier should be suppressed. If this option is specified the
   verifier will either print no output (in success cases) or just the
   error messages (in failure cases).

 - `--continue` means that the compiler will continue verification
   jobs beyond the first error (by default the compiler just stops at
   the first verification error encountered).

 - `-t SECONDS` or `--timeout SECONDS` sets the SMT solver timeout
   (for all solvers) to SECONDS. This overrides any `timeout` settings
   in the `babylon.toml` config file.

 - `--no-cache` means that the use of the `babylon.cache` file will be
   disabled. The compiler will neither read nor write this file. See
   "Files" below for more info about this file.


# Exit status

The compiler exits with status 0 if the requested job (compilation,
verification, etc.) was successful, or 1 if it failed.


# Environment

The compiler uses the `PATH` environment variable in the standard way
to search for any external commands that it invokes (such as the C
compiler or the SMT solvers).

The compiler also uses environment variables to determine where it
should look for its `babylon.toml` config file, as follows.

If the `XDG_CONFIG_HOME` environment variable is set, then the config
is assumed to be located in `$XDG_CONFIG_HOME/babylon/babylon.toml`.

Otherwise, if the `HOME` environment variable is set, the config is
searched for in `$HOME/.config/babylon/babylon.toml`.

If neither of those variables is set, then the compiler will fail with
an error message.


# Files

## Package Folders

A Babylon package folder (as passed to the `-r` command line option,
or found via the `-p` search path) contains various different files.
We document the most important ones below.

### Package manifest (`package.toml`)

`package.toml` is the package manifest file. This includes basic
metadata such as the name of the package, its dependencies, the list
of exported Babylon modules (if any), and so on. Further details can
be found in the "Babylon Package System" documentation.

### Source code folder (`src`)

This contains the source code for any Babylon modules that form part
of the package (in `.b` files). Some Babylon modules may also include
a C code component, in which case they will have a corresponding `.c`
file as well. This C code might also include other files (typically
`.h` header files) via the `#include` directive in which case these
other files will typically be present in the `src` directory as well.

### Build folder (`build`)

This folder is created by the `bab` compiler. It contains the output
of the compiler.

Note that the compiler only writes output to (and creates the `build`
folder in) the "root" package of the compilation (`-r` command line
option). "Dependency" packages do not receive a `build` folder nor
does the compiler write any sort of output to them.

The various files and folders that the compiler creates in `build` are
discussed further below.

### Verifier cache (`build/babylon.cache` file)

This is a cache used by the verifier. It is, basically, an SQLite
database file containing hashes of successfully completed
"verification problems". If the same verification problem is
encountered again in a future `bab verify` run, then it can be
skipped, since we already know it to be solvable.

The motivation for the cache is to speed up verification jobs. A large
program can easily take several minutes to verify (even on a fast
machine), so having a caching mechanism, which allows the compiler to
verify only parts of the program that have changed since the previous
run, can be highly advantageous.

Note that the cache works at three levels:
   
 - If the source code for an entire module (together with its imports)
   is unchanged since the previous (successful) verification, then
   that whole module can be skipped, since it is already known to be
   "good" from the previous verification.

 - Even when we do need to verify a module, we may find that the
   source code for some particular declaration (function, const, etc.)
   has not changed, and the declarations it depends on have also not
   changed, since the previous run. In this case, verification of that
   individual declaration can be skipped, since again it is "known
   good" from the previous verification.

 - Even when we do need to verify some declaration (e.g. a function),
   we may find that certain of the SMT problems generated for that
   declaration are identical to problems that were solved on a
   previous run. In this case, if the SMT problem was found to be
   `unsat` (i.e. verified) in a previous job, then it should still be
   `unsat` this time around, so that particular problem can be
   skipped.

Together, these three levels of caching typically result in
considerable time savings.

Note that using the cache does add a slight level of risk to
verification, as there is a risk that the cache file may end up
containing bad data for whatever reason, and also that the caching
system itself (in the `bab` compiler implementation) may contain bugs.
For that reason, it is recommended to occasionally do "full"
verification runs (perhaps as part of an overnight build) if one is
using the caching feature. This can be achieved by simply deleting the
`babylon.cache` file (it will be recreated in the next `verify` run)
or by using the `--no-cache` command line option.

If one does not trust the caching feature at all, then it can be
disabled completely in the compiler config file (see below).

### Generated C code files (`build/c` folder)

When a Babylon module is translated to C (by `bab compile` or `bab
build` or `bab translate`), the generated C code is placed in the
`build/c` directory (this is organised into subdirectories based on
package names).

### Generated object code files (`build/obj` folder)

When the C compiler is run (by `bab compile` or `bab build`), the
generated object code files (`.o` files) are placed in `build/obj`.

### Generated binary executable (`build/bin` folder)

When the linker is run (by `bab compile` or `bab build`), the final
generated executable is placed in `build/bin/NAME`, where NAME is the
package name of the root package.

Note that an executable is only generated if the root package contains
a `main-module` entry in its package manifest file. See the Babylon
Package System documentation for more details.


## Compiler Config File

Recall that the compiler uses a config file, named `babylon.toml`, and
normally located in `$HOME/.config/babylon/` (although this can be
changed via environment variables).

This file uses the [TOML format](https://toml.io/en/).

An example `babylon.toml` file, illustrating the general form of the
file, is shown below:

```
[packages]
paths = ["/path/to/package/dir", "/another/path"]

[c-compiler]
cc = "gcc"
ld = "gcc"
pkg-config = "pkg-config"
cflags = ["-O2"]
libs = ["-lsomelib"]

[verifier]
use-cache = true
max-processes = 0

[provers.z3]
command = "z3"
arguments = ["-in"]
timeout = 60
show-stderr = true
ignore-empty-output = false
ignore-exit-status = false
```

The individual configuration options are documented below.


### `[packages]` section

The `[packages]` section currently only has one available setting,
which is `paths`. This is a list of additional search directories for
Babylon packages. Specifying a path here is equivalent to adding an
extra `-p` option (with the given string as parameter) in every
compile, verify, or similar operation. Note the search order: paths in
`-p` options (from the command line) are searched first (in the order
given in the command line), and then paths from the config file are
searched afterwards (in the order given in the config file).

Note that this setting is optional; if not given, the default is `[]`
(i.e. only directories given via the command line `-p` option are
searched).


### `[c-compiler]` section

The `[c-compiler]` section sets the external C compiler and linker
programs that will be used by `bab compile` and `bab build` jobs. The
settings available are as follows.

 - `cc` sets the command to use for the C compiler, and `cflags` sets
   a list of additional command line arguments to pass to it.

   The `bab compile` command will call the given `cc` command to
   compile any generated `.c` files into `.o` files. The exact command
   line used is:

     `$cc $cflags $pkg_flags -I $include_dir -c $c_filename -o $o_filename`

   where:

     - `$cc` is the value of the `cc` setting.
     - `$cflags` is the list of strings given in the `cflags` setting.
     - `$pkg_flags` is a list of options taken from `pkg-config` (see
       below).
     - `$include_dir` is the path to any compiler-generated `.h` files
       needed.
     - `$c_filename` is the path to the compiler-generated `.c` file.
     - `$o_filename` is the path to the desired `.o` output file.

 - `ld` gives the linker command, and `libs` gives a list of
   additional arguments for the linker.

   The `bab compile` command will call the given linker to create the
   final executable file (from any `.o` files). The exact command line
   used is:

     `$ld -o $exe_name $o_files $libs $pkg_libs`

   where:

     - `$ld` is the value of the `ld` setting.
     - `$exe_name` is the path to the desired executable file (output
       from the linker).
     - `$o_files` is the list of `.o` files to be input to the linker.
     - `$libs` is the list of strings given in the `libs` setting.
     - `$pkg_libs` is a list of libraries taken from `pkg-config` (see
       below).

 - `pkg-config` is the name of a `pkg-config` command (or script). It
   can either be a full path, or the name of a command that can be
   found via the PATH environment variable. This command is run
   whenever a Babylon package includes a `system-packages` section in
   its `package.toml` file. (See the Babylon package system
   documentation for further details.)
   
     - Basically, if a Babylon package declares that it depends on a
       "system package" named NAME, at version VERSION, then the
       Babylon compiler will execute the command `$pkg_config --cflags
       NAME >= VERSION` to obtain additional C compiler flags, or
       `$pkg_config --libs NAME >= VERSION` to obtain additional
       linker command line options, when compiling any program that
       uses that Babylon package. (Here `$pkg_config` is the value of
       the `pkg-config` config setting.)

     - An exception is made for a system package named `math`. In this
       case, `pkg-config` is not run; instead, `-lm` is added to the
       linker command line (and nothing is added to the C compiler
       command line). This allows programs that use math functions
       (via external C code) to be compiled and linked easily, without
       needing to set linker flags manually. (Note that since `math`
       is a "fake" system package, any version specified for it is
       ignored. Setting the version to `""` is a common strategy.)

All of the above settings have defaults: if either `cc` or `ld` are
missing then they both default to `"gcc"`, and if `pkg-config` is
missing then it defaults to `"pkg-config"`. The `cflags` and `libs`
will be empty lists by default.


### `verifier` section

This specifies general settings for the verifier. The following
settings are currently available:

 - `use_cache` determines whether the `babylon.cache` file should be
   used. If this is `true`, then the verifier uses the `babylon.cache`
   file in the usual way. If `false`, then `babylon.cache` is neither
   read nor written -- it is as if the `--no-cache` command line
   option is always permanently enabled in every `bab verify` or `bab
   build` invocation. (See "Files" below for more information about
   `babylon.cache`.)

 - `max-processes` sets the maximum number of parallel SMT solver
   child processes that the `bab` command is willing to run
   simultaneously. This can be either a positive integer, or zero. If
   zero, this means that `bab` will decide for itself an appropriate
   setting, based on the available RAM and number of CPU cores on the
   machine. (A good strategy might be to set this to 0 initially and
   then use something like `top` to observe the state of your machine
   while a `bab verify` process is running. If you feel that the CPU
   and/or RAM of your machine are being either over- or
   under-utilised, you can then tweak the setting manually as
   desired.)

The defaults for the above are `true` for `use_cache`, and `0` for
`max-processes`.


### `provers` section(s)

These sections are used to configure the SMT solvers ("provers") that
the compiler uses.

Each prover section is named `[provers.NAME]` where NAME is a name for
the prover concerned (this NAME is used to refer to the prover
internally, e.g. in compiler log messages; it does not have to be the
same as the actual command name of the prover).

Under each prover section, the following settings may be configured.

 - `command` sets the command name of the prover, for example `z3` or
   `cvc5`. (This will be searched for on the PATH in the usual way, or
   alternatively, it may be set to an absolute path.)

 - `arguments` gives a list of strings which will be passed to the
   prover as command line arguments. Note that the compiler sends the
   SMT problem (in standard SMT-LIB format) to the prover on its
   standard input, and expects to receive the output (either `sat`,
   `unsat`, or `unknown`) from the prover's standard output, so the
   prover should be configured to operate in this way. For example,
   `z3` requires the `-in` command line flag to be passed (to tell it
   to read SMT-LIB commands from stdin).

 - `timeout` gives the time in seconds that the prover is allowed to
   run. If this time expires, and the prover is still running, then
   the `bab` command will send a signal (by default SIGTERM) to the
   prover to try to kill it. If the prover is still running after a
   certain further timeout (10 seconds by default) then a SIGKILL is
   sent as well.

 - `signal` sets the signal to be sent to the prover upon timeout.
   This can be specified either as a signal name (e.g. `"SIGINT"`) or
   a signal number (e.g. 2). (See `man 7 signal` for a list of signal
   numbers and names.)

 - `kill-timeout` sets the timeout (in seconds) between the sending of
   the initial timeout signal (see `signal` option) and the sending of
   a SIGKILL signal.

 - `ignore-exit-status`, if `false`, means that the Babylon compiler
   will print a warning message (to stderr) if the prover exits with
   any status code other than zero. If `true`, no such warning is
   printed.

 - `ignore-empty-output`, if `false`, means that the Babylon compiler
   will print a warning message (to stderr) if the prover exits
   without printing anything to stdout. If true, no such warning will
   be printed in this case. Note that, regardless of the setting
   `ignore-empty-output`, the Babylon compiler will always print a
   warning message (to stderr) if any prover prints something other
   than `sat`, `unsat` or `unknown` to stdout; so this setting only
   applies when the stdout from the prover is completely empty.

 - `show-stderr`, if `true`, means that any stderr output from the
   prover will be passed through and printed to the `bab` command's
   own stderr output. If `false`, stderr output from the prover will
   be redirected to `/dev/null` instead. (This setting is useful for
   "chatty" provers that like to print "progress" or "log" type
   messages on their stderr; we normally do not want to see these
   during a verify job.)

The defaults for the above are:
 - `command` is required; not specifying this is an error.
 - `arguments` defaults to `[]`.
 - `timeout` defaults to `60` and `kill-timeout` to `10`.
 - `signal` defaults to `"SIGTERM"`.
 - `ignore-exit-status` and `ignore-empty-output` default to `false`.
 - `show-stderr` defaults to `true`.


# Bugs

Currently the compiler is only a prototype and as such, it is expected
that it may contain bugs.

Any bugs found will be listed here once the details become known.


# Examples

The compiler ships with several example packages in the `packages`
folder of the distribution.

These fall into three categories:

 - `chess` is a complete example program.

 - The fifteen packages whose names begin `example` are a series of
   example programs, which form a tutorial of sorts, and illustrate
   various features of the Babylon language.

 - The remaining packages (`coretypes`, `datetime`, `gfx-engine`, `io`
   and `random`) are a set of ready-to-use "libraries" which can be
   used in Babylon programs.


# See also

[Babylon Language Reference Manual](lang-ref.md)

[Babylon Package System](package.md)

[Babylon/C Interface](c-interface.md)

[TOML File Format](https://toml.io/en/)
