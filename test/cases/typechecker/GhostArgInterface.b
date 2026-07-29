module GhostArgInterface
interface {
    function f1(ghost x: i32);
    function f2(ref ghost x: i32);
    function f3(x: i32);
    function f4(ghost x: int);  // OK, ghost arg may have a non-runtime type
}
function f1(ghost x: i32) {}  // OK, matches
function f2(ref ghost x: i32) {}  // OK, matches
function f3(ghost x: i32) {}  // Error: interface has non-ghost, impl has ghost
function f4(ghost x: int) {}  // OK, matches
