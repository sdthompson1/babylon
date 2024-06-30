// Types cannot be 'ghost'

module BadGhost
interface {
    ghost datatype Foo = A | B | C;
}
