module AbsType

interface {
    type Foo : Default+Copy;

    ghost function valid_foo(foo: Foo): bool;

    function reset_foo(ref foo: Foo)
    {
        var default_foo: Foo;
        foo = default_foo;
    }

    function new_foo(): Foo
        ensures valid_foo(return);

    function get_foo_value(foo: Foo): i32
        requires valid_foo(foo);

    function set_foo_value(ref foo: Foo, x: i32)
        requires valid_foo(foo);
        ensures valid_foo(foo);
        ensures get_foo_value(foo) == x;
}

datatype Foo = BadFoo | Foo(i32);

ghost function valid_foo(foo: Foo): bool
{
    match foo {
    case BadFoo => return false;
    case Foo(_) => return true;
    }
}

function new_foo(): Foo
    ensures valid_foo(return);
{
    return Foo(0);
}

function get_foo_value(foo: Foo): i32
    requires valid_foo(foo);
{
    match foo {
    case Foo(n) => return n;
    }
}

function set_foo_value(ref foo: Foo, x: i32)
    requires valid_foo(foo);
    ensures valid_foo(foo);
    ensures get_foo_value(foo) == x;
{
    match foo {
    case Foo(ref n) => n = x;
    }
}
