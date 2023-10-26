
// This is the first demonstration program for the "Babylon"
// programming language.

// Here we will just make a simple "Hello World" program.


// Each Babylon source code file must begin by declaring the module name,
// as follows. (The module name must match the filename.)

module Demo_01_HelloWorld


// We must now specify the "interface" for the module. The interface
// is the list of functions, constants and types exported by the
// module. This module will export just one function called "main".
// "main" is the entry point for the program.

interface {
    function main();
}


// The next thing we need is a "print" function. Unfortunately, the Babylon
// language does not (yet) come with any kind of "standard library", so there
// is no "print" function (or any similar function) built in.

// So, for now, what we have to do is write some C functions to print strings
// (or whatever else we need) and then import those functions into the Babylon
// program.

// For the sake of these examples/demos, I have provided a small C file
// "example_lib.c", and corresponding Babylon module "ExampleLib.b", providing
// functions "print_i32", "print_string" and some others. To use this we must
// import it, as follows:

import ExampleLib;


// We are now ready to give the definition of "main", as follows.

function main()
{
    // Here we will just call "print_string" (from the ExampleLib),
    // passing our hello world message.
    // Notice that we have to include a newline character ("\n") at
    // the end of the string, as print_string doesn't do this
    // automatically.
    print_string("Hello, world!\n");
}


// To compile and run this program, assuming you have the "babylon"
// compiler available on your PATH, you first need to run the
// following command:

// babylon -c Demo_01_HelloWorld.b

// This will compile the "Demo_01_HelloWorld.b" module, as well as
// all Babylon modules that it imports (i.e. "ExampleLib.b"), into
// assembly code files (*.s files).

// (If you want to put the *.s files into a separate directory, you can
// add the "-o" option, e.g. "babylon -c Demo_01_HelloWorld.b -o build"
// will put the files in a "build" directory.)

// To produce an executable, these *.s files must be given to gcc, together
// with example_lib.c (which contains the C functions we are using, as
// discussed above):

// gcc Demo_01_HelloWorld.s ExampleLib.s example_lib.c

// This should produce an executable "a.out" in the current directory.
// Running this, you should then hopefully see the "Hello, world!"
// message on your screen!
