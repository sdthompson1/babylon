module AllocatedAbstract

interface {
    type T (allocated_always);
    type U (allocated_always);
}

// Realize T by a non-allocated type
type T = i32;

// Realize U by an allocated-always (extern) type
extern type U (allocated_always);

function test2() {
    var x: T;   // This is legal, because the implementation can see that T isn't "really"
                // allocated_always, even though it's declaration says that it is.

    var y: U;   // Error, U is allocated - even in the implementation.
}
