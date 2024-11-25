// Example 1 -- A simple "Hello World" program.
// This example will explain some of the basic syntax of the language.


// Each Babylon source code file must begin by declaring the module name,
// as follows. (The module name must match the filename.)

module Example01


// We must now specify the "interface" for the module. The interface
// is the list of functions, constants and types exported by the
// module. This module will export just one function called "main",
// which will be the entry point for the program.

interface {
    function main();
}


// We can now import any other modules required.

// For this program, we import the Console module, which contains a
// function called "println".

import Console;


// We are now ready to give the definition of "main", as follows.

function main()
{
    println("Hello, world!");
}
