module ModBoundary

// "a % b" has the same precondition as "a / b": b must be nonzero, and the
// quotient must not overflow. The quotient overflows in one case only: the
// minimum value of a signed type, divided by -1. So "MIN % -1" is not
// allowed, although the remainder (zero) would be in range; in C,
// "INT_MIN % -1" is undefined behaviour. (The verifier's side of this is
// tested in test/cases/verifier/Division.b, and compile-time constants in
// test/cases/typechecker/ConstModOverflow.b.)
//
// This test checks the cases next to the forbidden one, which are allowed,
// with operands that are not known at compile time.

interface { function main(); }
import Test;

// (I32_MIN and I32_MAX come from the Test module.)
const I64_MIN: i64 = -9223372036854775808;
const I64_MAX: i64 = 9223372036854775807;

function mod_i8(a: i8, b: i8): i8
    requires b != 0;
    requires !(a == -128 && b == -1);
{
    return a % b;
}

function mod_i32(a: i32, b: i32): i32
    requires b != 0;
    requires !(a == I32_MIN && b == -1);
{
    return a % b;
}

function mod_i64(a: i64, b: i64): i64
    requires b != 0;
    requires !(a == I64_MIN && b == -1);
{
    return a % b;
}

function div_i32(a: i32, b: i32): i32
    requires b != 0;
    requires !(a == I32_MIN && b == -1);
{
    return a / b;
}

function main()
{
    print_i8(mod_i8(-128, 1));        // 0
    print_i8(mod_i8(-127, -1));       // 0
    print_i8(mod_i8(-128, -2));       // 0
    print_i8(mod_i8(-128, -3));       // -2
    print_i8(mod_i8(-128, 127));      // -1

    print_i32(mod_i32(I32_MIN, 1));          // 0
    print_i32(mod_i32(I32_MIN + 1, -1));     // 0
    print_i32(mod_i32(I32_MIN, -2));         // 0
    print_i32(mod_i32(I32_MIN, -3));         // -2
    print_i32(mod_i32(I32_MIN, I32_MAX));   // -1
    print_i32(mod_i32(I32_MAX, -1));         // 0

    print_i64(mod_i64(I64_MIN, 1));          // 0
    print_i64(mod_i64(I64_MIN + 1, -1));     // 0
    print_i64(mod_i64(I64_MIN, -2));         // 0
    print_i64(mod_i64(I64_MIN, -3));         // -2
    print_i64(mod_i64(I64_MIN, I64_MAX));   // -1

    print_i32(div_i32(I32_MIN, 1));          // -2147483648
    print_i32(div_i32(I32_MIN + 1, -1));     // 2147483647
    print_i32(div_i32(I32_MIN, -2));         // 1073741824
}
