// Only functions and types can be 'extern' currently

module BadExtern
interface {
    extern const foo: i32 = 100;
}
