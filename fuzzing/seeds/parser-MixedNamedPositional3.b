module Main
interface {
    function f() {
        match 1 {
        case {p1, x=p2} =>   // Error: mixed named and positional fields in pattern
        }
    }
}
