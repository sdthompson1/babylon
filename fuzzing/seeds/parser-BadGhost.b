// Types cannot be 'ghost'

module Main
interface {
    ghost datatype Foo = A | B | C;
}
