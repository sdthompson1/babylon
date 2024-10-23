module ExternType

interface {
    function main();
}

import Test;


extern type Foo: Default+Copy;

function foo(x: Foo)
{
}

function main()
{
    var v: Foo;
    foo(v);
}
