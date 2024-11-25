// Example 4 -- Casts.

// In this example we briefly discuss numeric casts (i.e. converting
// values from one integer type to another).

module Example04

interface {
    function main();
}

import Console;

function fun1()
{
    // Create some variables of types i32 and u16.
    var x: i32 = 100;
    var y: u16 = 50;

    // When assigning to a variable of a different type, the system will
    // automatically "cast" (convert) the value to the correct type. For
    // example, in the below, the value of x is automatically converted
    // from i32 to u16 before the assignment.
    y = x;

    // We can also use the notation "u16(x)" to make this conversion
    // explicit, if we wish.
    y = u16(x);   // convert x to u16, then assign to y.

    // The alternative syntax "cast<u16>(x)" is also available.
    y = cast<u16>(x);

    // When converting it is possible that the value might be outside the
    // range of the target type. In this case a verification error will be
    // generated. For example:
    x = 1000000;   // this is fine, because 1000000 is within the i32 range.
    
    // y = x;      // this would produce a verification error, because it is
                   // trying to convert 1000000 to u16, which is not possible
                   // (the max possible u16 is 65535).

    // y = u16(-1);  // this would also produce an error, because -1 cannot be
                     // converted to an unsigned type.
}

function fun2()
{
    var x: i32 = 100;
    var y: i16 = 10;
    var a: u16 = 10;
    var b: i16 = 20;


    // During binary operations such as "+" we might encounter two different
    // types. In this case, the operands will be converted to the smallest
    // integer type that can hold the full range of both operands.

    // For example:

    // Here, x is i32 and y is i16. The smallest type that can hold all
    // possible i16 and i32 values is i32. So the operands are both converted
    // to i32 and then the addition is done.
    // (In other words, the following is equivalent to "var z = x + i32(y);".)
    var z = x + y;

    // Here, we have one u16 and one i16 operand. The smallest type that can
    // hold the full range of both u16 and i16 is i32. So "c" will end up having
    // type i32.
    var c = a + b;

    // The exception to the above rule is when the operands have types i64 and
    // u64. In this case, there is no common type that can hold the full range
    // of both operands. Instead, the rule is that the result has type u64.
    // So in the following, d has type u64.
    var d = i64(1) + u64(2);


    // Note that plain integer constants (such as "1" and "2") are considered
    // to have type i32 by default (exception: if the constant is outside the
    // i32 range, then u32, i64 or u64 may be used instead).

    // For example:

    var p = 100;     // p has type i32

    var q = 9999999999;   // q has type i64 (value is above I32_MAX but below I64_MAX)

    var r = 9999999999999999999;   // r has type u64 (value is above I64_MAX but below U64_MAX)

    // var s = 99999999999999999999;  // compile time error (value is above U64_MAX)
}

function f(x: u8): u8
{
    // This is showing some bitwise operators -- "&" is bitwise AND,
    // "|" is bitwise OR.
    return (x & 12) | 7;
}

function fun3(x: i32)
    requires 0 <= x <= 255;
{
    // When calling a function, the parameters passed are automatically cast
    // to the correct types if necessary. Again, the verifier will prove that
    // the arguments are in the correct range, if required.

    // The following works because even though 100 is interpreted as i32, it
    // can be automatically converted to u8 without any problems.
    var a = f(100);

    // The following works because of the precondition (above) that x is
    // between 0 and 255 (which coincides with the u8 range).
    var b = f(x);

    // The following would fail verification, because x + 1 might be outside
    // the u8 range.
    // var c = f(x + 1);

    // (Note: The error message produced for the above is "Operator 
    // precondition might not be met", which is not very clear unfortunately.
    // The compiler should probably say something like "Implicit conversion
    // to u8 is not possible" or something like that. This is something to
    // fix in a future version!)
}


function main()
{
    print_i32(f(13));
    println("");
}


