module GhostExternIncomplete

interface {}

// Ghost extern functions are not checked for "return value not
// allocated" (ghost code has no such requirement), so they may return
// incomplete types, and allocated values.

type State = {
    flags: bool[],
    count: u32
};

extern type Handle (allocated);

ghost extern function get_state(x: u32): State;
    ensures sizeof(return.flags) == u64(x);

ghost extern function get_array(): u8[];

ghost extern function get_handle(): Handle;
    ensures allocated(return);

function test1()
{
    ghost var s = get_state(10);
    ghost var a = get_array();
    ghost var h = get_handle();
    assert sizeof(s.flags) == u64(10);     // OK, follows from the postcondition
    assert allocated(h);                   // OK, follows from the postcondition
    assert sizeof(a) == u64(0);            // Fails, nothing is known about get_array
}
