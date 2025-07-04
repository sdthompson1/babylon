module MixedNamedPositional1
interface {
    function f() {
        var tup = { x=1, false };   // Error: mixed named and positional fields in term
    }
}
