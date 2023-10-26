module TypedefDuplicate
interface {

type Foo = i32;    // Error, duplicate definition of Foo

}

type Foo = i32;
