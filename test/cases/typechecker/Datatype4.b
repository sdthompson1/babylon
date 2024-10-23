module Datatype4

interface {}

extern type Unmovable;  // no traits

datatype Foo = Foo0(Unmovable) | Foo1;
datatype Bar<a> = Bar0(a) | Bar1;

function test1()
{
    var a = Foo1;                  // error, Foo doesn't have Move trait
    var b = Bar1<Unmovable>;       // error, Bar<Unmovable> doesn't have Move trait
    var c = Bar1;                  // ok, Bar<bool> is inferred, and this has Move
    var d: Bar<Unmovable> = Bar1;  // error, tries to unify Bar<alpha_Move> with Bar<Unmovable>, fails
}  // error: d was not dropped
