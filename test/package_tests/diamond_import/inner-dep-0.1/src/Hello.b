module Hello

interface {
    function say_hello();
}

import Test;

function say_hello()
{
    print_string("Hello from inner-dep-0.1\n");
}
