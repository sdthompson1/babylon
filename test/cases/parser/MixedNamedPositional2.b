module MixedNamedPositional2
interface {
    function f(x: {i32, fld: i32});   // Error: mixed named and positional fields in type
}
