module ExternTypeDef

interface {
    extern type Foo = i32;   // error, extern type cannot have definition
}
