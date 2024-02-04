module Bitwise
interface { function main(); }

// Compile-time evaluation of bitwise and logical operators.

import Test;

const bit_and: i32 = i32(15) & i32(20);
const bit_or:  u32 = u32(15) | u32(20);
const bit_xor: u8  = u8(15) ^ u8(20);

const complex: i64 = (((3 | 4) ^ 2) & i64(7)) + 1;
const negative: i8 = (i8(-128) | i8(1)) + i8(127) + i8(127);

const shl: i32 = 3 << 5;
const shr: i8 = i8(12) >> i8(1);
const shr_neg: i32 = -3 >> u8(1);
const shr_neg_2: i32 = -75 >> 3;
const shr_u: u16 = u16(8) >> u64(2);
const shl_zero: i32 = 10 << 0;
const shr_zero: i32 = 20 >> 0;

const shl_plus: i32 = (3 << 5) + 1;
const shr_plus: i32 = (5 >> 2) + 1;

const complement: u8 = ~ u8(129);
const complement_signed: i8 = ~ i8(10);
const not_true: bool = !true;
const not_false: bool = !false;

const and1: bool = true && false;
const and2: bool = true && true;
const and3: bool = false && (1/0 == 1);    // Short circuiting

const or1: bool = false || true;
const or2: bool = false || false;
const or3: bool = true || (1/0 == 1);   // Short circuiting

const imp1: bool = true ==> true;
const imp2: bool = true ==> false;
const imp3: bool = false ==> (1/0 == 1);  // Short circuiting

const impby1: bool = true <== true;
const impby2: bool = false <== true;
const impby3: bool = (1/0) == 1 <== false;   // Short circuiting

const iff1: bool = true <==> true;
const iff2: bool = true <==> false;

const imp_right_assoc: bool = false ==> false ==> false;
const imp_brackets:    bool = (false ==> false) ==> false;

// This will be accepted by the constant-evaluator (even though strictly speaking
// the shift count is too big for an 8-bit operand), but it produces zero.
const shr_too_much: u8 = u8(255) >> 8;

function main()
{
    Test.print_i32(bit_and);
    Test.print_u32(bit_or);
    Test.print_u8(bit_xor);

    Test.print_i64(complex);
    Test.print_i8(negative);

    Test.print_i32(shl);
    Test.print_i8(shr);
    Test.print_i32(shr_neg);
    Test.print_i32(shr_neg_2);
    Test.print_u16(shr_u);
    Test.print_i32(shl_zero);
    Test.print_i32(shr_zero);

    Test.print_i32(shl_plus);
    Test.print_i32(shr_plus);

    Test.print_u8(complement);
    Test.print_i8(complement_signed);
    Test.print_bool(not_true);
    Test.print_bool(not_false);

    Test.print_bool(and1);
    Test.print_bool(and2);
    Test.print_bool(and3);

    Test.print_bool(or1);
    Test.print_bool(or2);
    Test.print_bool(or3);

    Test.print_bool(imp1);
    Test.print_bool(imp2);
    Test.print_bool(imp3);

    Test.print_bool(impby1);
    Test.print_bool(impby2);
    Test.print_bool(impby3);

    Test.print_bool(iff1);
    Test.print_bool(iff2);

    Test.print_bool(imp_right_assoc);
    Test.print_bool(imp_brackets);

    Test.print_u8(shr_too_much);
}
