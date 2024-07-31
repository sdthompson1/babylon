module Foo
interface {
    // Compared to previous test, this changes i8 to i16
    datatype Foo = FooCtor(i16);
    const foo: Foo;
}

const foo: Foo = FooCtor(0);
