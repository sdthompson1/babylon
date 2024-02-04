module ConstErrors
interface{}

function f(): i32
{
    return 0;
}

function fb(): bool
{
    return false;
}

const INT64_MIN = -9223372036854775808;

// Error, not a compile time constant.
// (The compiler isn't smart enough to actually evaluate the function calls at
// compile time.)

const c1 = f();
const c2 = if fb() then 1 else 2;
const c3 = ~ f();
const c4 = INT64_MIN / -1;   // Compile time overflow
const c5 = 1 / 0;            // Compile time division by zero
const c6 = f() + 1;
const c7 = 1 + f();
const c8 = { 1, f() };
const c9 = { a=f(), b=1 };
const c10 = {{ x=1, y=2 } with x=3, y=f() };
const c11 = let a = 10 in a+1;   // ok
const c12 = let a = f() in a+1;  // not ok

ghost const cg = f();   // ok, ghost constants are exempt from the "known at compile time" rule.

const c13 = 1 << 999;   // invalid shift count
const c14 = i8(1000);   // cast out of range
const c15 = -(-9223372036854775808);   // negating I64_MIN
const c16 = -(-2147483648);  // negating I32_MIN
const c17 = u8(100) + u8(200);   // u8 + overflow
const c18 = i8(100) + i8(100);   // i8 + overflow
const c19 = u8(100) - u8(101);   // u8 - overflow
const c20 = i8(-100) - i8(100);  // i8 - overflow
const c21 = u64(10376293541461622784) + u64(10376293541461622784);  // u64 + overflow
const c22 = i64(8070450532247928832) + i64(8070450532247928000);    // i64 + overflow
const c23 = u64(1) - u64(2);  // u64 - overflow
const c24 = i64(-8070450532247928832) - i64(8070450532247928832);  // i64 - overflow
const c25 = i64(-9223372036855) * i64(1000001);  // i64 * overflow
const c26 = u64(18446744073709552) * u64(1000);  // u64 * overflow
const c27 = -1 >> 64;  // invalid shift count

// These next examples are valid shift counts (the constant-evaluation code
// can shift upto 63 places, even if the type is less than 64-bits) but the
// first one produces an overflow.
const c28 = 1 << 33;  // overflow
const c29 = 1 >> 33;  // valid, produces 0

// Pattern match failure at compile-time
const c30 =
    match ({1,true}) {
      case {2,true} => 0
    };
