module AllocatedAbstract

interface {
    type T (allocated*);
    type U (allocated*);
}

// Realize T by a non-allocated type
type T = i32;

// Realize U by an allocated* (extern) type
extern type U (allocated*);

function test2() {
    var x: T;   // This is legal, because the implementation can see that T isn't "really"
                // allocated*, even though it's declaration says that it is.

    var y: U;   // Error, U is allocated - even in the implementation.
}
