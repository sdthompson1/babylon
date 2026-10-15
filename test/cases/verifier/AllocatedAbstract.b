module AllocatedAbstract

interface {
    type T (allocated_always);

    datatype D = D(T);

    type U;

    function test1() {
        var x: T;    // Error: creating an allocated_always value
    }
}

// Realize T by a non-allocated type
type T = i32;

function test2() {
    var x: T;   // This is now legal, because the implementation can see that
                // T isn't "really" allocated_always, even though it's declaration
                // says that it is.
}
