module CallAbstract

import Test;

interface {
    // Define an "abstract" function i.e. one that is declared in the
    // interface, but only defined in the implementation.
    function abstract_fun();

    // Call the "abstract" function from the interface.
    // (Previously this was causing an internal compiler error.)
    function main()
    {
        abstract_fun();
    }
}

function abstract_fun()
{
    print_string("Hello!\n");
}
