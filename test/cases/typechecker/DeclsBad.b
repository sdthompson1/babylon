module DeclsBad
interface {
    const x: i32 = true;    // Const doesn't match claimed type
    const r: i32 = r + 1;   // Illegal recursion
    const a;                // Incomplete definition (type not stated in the interface)
    const b;                // Incomplete definition (type not stated in interface, and no implementation)
    const c: i32;           // Missing implementation - not reported because of above errors
    function f(): i32;      // Missing implementation - not reported because of above errors
}
