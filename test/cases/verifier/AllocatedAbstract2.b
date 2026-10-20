module AllocatedAbstract2

interface {
    type T (allocated*);

    function test1() {
        var x: T;   // Error, T is allocated*, as far as the interface knows.
    }
}

// T is realized by a non-allocated type, but function test1 doesn't know that,
// so this doesn't prevent the error.
type T = i32;
