module AbstractType3

interface {
    type Foo;
}

// This is declaring Foo to have kind * -> *, but in the interface it had kind *.
datatype Foo<a> = FooCtor(a);
