module ExternType2

interface {
    extern type Foo;
}

extern type Foo;   // Illegal, duplicate definition.
