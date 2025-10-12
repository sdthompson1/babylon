module Main

interface {
    extern type Foo;
}

extern type Foo;   // Illegal, duplicate definition.
