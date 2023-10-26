module BadTyarg
interface {
  const x: T<a,b+>;   // rogue "+" character
}
