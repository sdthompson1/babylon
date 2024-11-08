module A

interface {
    function func();
}

import Hello;   // imports from dep2

function func()
{
    say_hello();
}
