module ExternType

interface {
    function main();
}

import Test;


extern type Foo: Default;

function foo(x: Foo)
{
}

function main()
{
    var v: Foo;
    foo(v);
}
