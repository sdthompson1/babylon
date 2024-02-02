
// This is the fourth demonstration program for the Babylon language.

// In this file we briefly discuss numeric casts (i.e. converting values
// from one integer type to another).

module Demo_04_Casts

interface {
    function main();
}

import ExampleLib;

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
    // types. In this case, both operands will be converted to a suitable
    // common type. For example:

    // Below, y is converted to i32 so that the addition can be done.
    // (In other words, the following is equivalent to "var z = x + i32(y);".)
    var z = x + y;

    // Below, a and b will both be converted to i32. This is because i32 is
    // the smallest type that can represent the full range of both u16 and
    // i16. So "c" will end up having type i32.
    var c = a + b;


    // If no suitable common type is available, a type error will result. For
    // example, there is no type that can represent all values of both i64 and
    // u64, so the following addition will fail.
    // var d = i64(1) + u64(2);


    // Note that plain integer constants (such as "1" and "2") are considered
    // to have type i32 by default (exception: if the constant is outside the
    // i32 range, then u32, i64 or u64 may be used instead).

    // For example:

    // This next line works, because the 100 is initially interpreted as i32,
    // but is then converted to u64 for assignment to p. The conversion from
    // i32 to u64 does not produce any problems.
    var p: u64 = 100;

    // This next expression "p == 100" fails, because there is no common type
    // that can be used for the comparison between p (a u64 value) and 100 (an
    // i32 value).
    // if p == 100 { print_string("Hello\n"); }

    // To solve this we have to explicitly state that 100 is to be interpreted
    // as a u64 value:
    if p == u64(100) { print_string("Hello\n"); }


    // Note: The above is a common nuisance that often comes up when working
    // with 64-bit types. I will probably try to fix this in a future version
    // of the language. (The solution would be for the system to be more
    // flexible about integer constants; instead of just assuming that an
    // integer constant is i32, it should try to guess a suitable type that
    // would work within the surrounding context.) For now though, be aware
    // that explicit casts might be needed, especially when working with i64
    // or u64 values.
}

function f(x: u8): u8
{
    // (This is showing some bitwise operators -- "&" is bitwise AND,
    // "|" is bitwise OR.)
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
}


// To verify this example:
//   babylon -V Demo_04_Casts.b

// To run this example:
//   babylon -c Demo_04_Casts.b
//   gcc Demo_04_Casts.c ExampleLib.c example_lib.c
//   ./a.out
