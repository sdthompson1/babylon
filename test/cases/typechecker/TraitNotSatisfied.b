module TraitNotSatisfied

interface {}

type Typedef<a: Copy> = a;

function func<a: Drop>() {}

function test()
{
    var x: Typedef<i32[]>;   // error: Typedef<i32[]> doesn't have Default
    func<i32[*]>();          // error: i32[*] doesn't satisfy Drop
}


function f2<T: Copy>(x: T): T
{
    return x;
}

function f3<T: Drop>(x: T): i32
{
    return 0;
}

extern type MyType : Copy + Default;

function test2()
{
    var m1: MyType;
    var m2 = f2(m1);  // ok
    var m3 = f2(m2);  // ok

    var i = f3(m3);  // error: MyType does not have Drop trait

    var j = f3({100, m1});  // error: the record doesn't have Drop, because one of its fields doesn't.
    var k = f3({100, 200}); // this is ok, all fields have Drop
}


datatype DatatypeTest1 = A | B(i32);
datatype DatatypeTest2 = C | D(i32) | E(MyType);

function test3()
{
    func<DatatypeTest1>();   // ok, all variants support Drop
    func<DatatypeTest2>();   // error, the "E" variant does not support Drop.
}
