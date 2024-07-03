module DeclsBad2
interface {
    const c: i32;           // Valid here, but the implementation is wrong
    function f(): i32;      // Valid here, but the implementation is wrong
}

const c: i32;           // Incomplete definition (no right-hand-side in implementation)  
const d: i32;           // Same (but without a corresponding interface this time)

function f(): i32;      // Incomplete definition
function g(): i32;      // Incomplete definition w/o corresponding interface

function rec_attr(): bool
    requires rec_attr();  // Illegal, cannot use function in its own attributes (currently)
    ensures rec_attr();   // Ditto
{
    return true;
}

function assign_to_param(x: i32)
{
    x = 1;   // This is not allowed, args are considered const.
}
