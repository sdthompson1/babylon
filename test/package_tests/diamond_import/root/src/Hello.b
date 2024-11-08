module Hello

interface {
    function say_hello();
}

import Test;

function say_hello()
{
    // This should not be called, as only dep1 and dep2 import Hello;
    // nothing in the root package imports Hello.
    print_string("Hello from root package\n");
}
