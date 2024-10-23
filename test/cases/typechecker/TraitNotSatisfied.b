module TraitNotSatisfied

interface {}

import Test;

type Typedef<a: Copy> = a;

function func<a: Copy>() {}
function func2<a: Copy>(x: a) {}

function test()
{
    var x: Typedef<i32[]>;   // error: Typedef<i32[]> doesn't have Default
    func<i32[*]>();          // error: i32[*] doesn't satisfy Copy

    var a = alloc_array<i32>(10);
    func2(a);  // error: i32[*] doesn't satisfy Copy
    free_array(a);
}

extern type MyType : Move + Default;

datatype DatatypeTest1 = A | B(i32);
datatype DatatypeTest2 = C | D(i32) | E(MyType);

function test3()
{
    func<DatatypeTest1>();   // ok, all variants support Copy
    func<DatatypeTest2>();   // error, the "E" variant does not support Copy
}
