module IntReal

interface {}

function f1()
{
    var i: int;    // Not allowed
    ghost var ig: int;   // OK

    var r: real;   // Not allowed
    ghost var rg: real;  // OK
}

function f2(x: real, i: int): int    // Not allowed
{
    var v = int(0);    // cast to int not allowed in executable code
    return v;          // Won't report error, because the return-type of the function wasn't accepted
}

ghost function f3(x: real, i: int): int   // OK because ghost function
{
    return int(0);   // OK because ghost function
}

ghost function f4()
{
    var i: int = int(100);
    while i > int(0)
        decreases i;     // 'int' decreases value is accepted
    {}

    var r: real = real(1);
    while r > real(0)
        decreases r;     // this is now accepted as well (but verifier will fail)
    {}
}

ghost function f5()
{
    // +, -, etc. work, but mixed types not allowed
    var x1 = i32(1) + int(2);    // error
    var x2 = int(1) + int(2);    // ok
    var x3 = real(1) + real(2);  // ok

    // bitwise operators not allowed on int or real
    var x4 = int(1) & int(2);    // error
    var x5 = real(1) & real(2);  // error

    // similarly for shifts
    var x6 = int(1) << int(3);    // error
    var x7 = real(1) >> real(3);  // error

    // modulo only works on int, not real
    var x8 = int(1) % int(2);    // ok
    var x9 = real(1) % real(2);  // error

    // division works on both int and real
    var x10 = int(1) / int(2);    // ok
    var x11 = real(1) / real(2);  // ok

    // unary negation works
    var x12 = - int(1);         // ok
    var x13 = - real(2);        // ok

    // unary ~ doesn't work with int or real
    var x14 = ~ int(1);    // error
    var x15 = ~ real(2);   // error
}

datatype ContainsInt = A(i32) | B(int);

function f6()
{
    // tuple or variant containing invalid type
    var x: {i32, int};    // error
    var y: ContainsInt;   // error

    ghost var gx: {i32, int};   // OK
    ghost var gy: ContainsInt;  // OK
}

const c1 = real(2);  // Error, cannot have real consts
const c2 = int(3);   // Error, cannot have int consts
const c3: real = 0;  // Error
const c4: int = 0;   // Error

type BadRecord = {i32, int};
const c5: BadRecord = {2, int(3)};   // Error, "int" embedded within a record
