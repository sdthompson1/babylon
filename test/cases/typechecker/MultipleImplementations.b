module MultipleImplementations
interface {
    const x: i32 = 1;

    datatype DT1 = DT1;
    datatype DT2 = DT2;

    ghost function foo();
    ghost function bar() {}
}


const x: i32 = 1;          // Error

datatype DT1 = DT1;        // Error
datatype DT2 = XYZ;        // Error

ghost function foo() {}    // OK
ghost function bar() {}    // Error
