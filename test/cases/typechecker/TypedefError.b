module TypedefError
interface {}

type Foo = i32;

function f(x: Foo)
{
    if (x) {    // Error: Foo doesn't match bool
    }
}
