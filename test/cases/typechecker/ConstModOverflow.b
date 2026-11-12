module ConstModOverflow
interface {}

// "a % b" is an error whenever "a / b" is. In particular, if the quotient
// overflows (the minimum value of a signed type, divided by -1) then "%"
// is an error too, although the remainder itself (zero) would be in range.
// (This is the verifier's rule for "%" at runtime, see
// test/cases/verifier/Division.b; "INT_MIN % -1" is undefined behaviour
// in C.)

const I64_MIN = -9223372036854775808;
const I32_MIN = -2147483648;

const c1 = I64_MIN % -1;             // Error
const c2 = I32_MIN % -1;             // Error
const c3 = i16(-32768) % i16(-1);    // Error
const c4 = i8(-128) % i8(-1);        // Error

// These are fine.
const ok1 = I64_MIN % 1;
const ok2 = (I64_MIN + 1) % -1;
const ok3 = I32_MIN % 1;
const ok4 = (I32_MIN + 1) % -1;
const ok5 = I32_MIN % -2;
const ok6 = i8(-128) % i8(1);
const ok7 = i8(-127) % i8(-1);
const ok8 = u8(255) % u8(1);
