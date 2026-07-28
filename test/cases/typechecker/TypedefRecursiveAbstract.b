module TypedefRecursiveAbstract

interface {
    type T;
    datatype Foo = Mk(T);

    type U;
    type V = {a: U};
}

// Error: T recursively defined in terms of itself,
// via a previous datatype definition
type T = Foo;

// Error: U recursively defined in terms of itself,
// via a previous typedef
type U = V;
