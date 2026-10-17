module TypedefRecursiveAbstract2

interface {
    type T1;
    datatype Foo1 = Mk1(T1);
    datatype Bar1 = MkBar1(Foo1);

    type T2;
    datatype Foo2 = Mk2(T2);

    type T3;
    datatype Foo3 = Mk3(T3);
}

// Error: T1 recursively defined in terms of itself,
// via two previous datatype definitions
type T1 = Bar1;

// Error: T2 recursively defined in terms of itself,
// via a typedef in the implementation and a datatype in the interface
type W2 = Foo2;
type T2 = W2;

// Error: T3 is realized by a datatype which is mutually recursive
// with a datatype in the interface
datatype T3 = MkT3(Foo3) | Nil3;
