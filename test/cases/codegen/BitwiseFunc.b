module BitwiseFunc
interface { function main(); }

// Bitwise and logical operators

import Test;

function main()
{
    var bit_and: i32 = i32(15) & i32(20);
    var bit_or:  u32 = u32(15) | u32(20);
    var bit_xor: u8  = u8(15) ^ u8(20);

    var complex: i64 = (((3 | 4) ^ 2) & i64(7)) + 1;
    var negative: i8 = (i8(-128) | i8(1)) + i8(127) + i8(127);

    var shl: i32 = 3 << 5;
    var shr: i8 = i8(12) >> i8(1);
    var shr_neg: i32 = -3 >> u8(1);
    var shr_u: u16 = u16(8) >> u64(2);

    var shl_plus: i32 = (3 << 5) + 1;
    var shr_plus: i32 = (5 >> 2) + 1;

    var complement: u8 = ~ u8(129);
    var complement_signed: i8 = ~ i8(10);
    var not_true: bool = !true;
    var not_false: bool = !false;

    var and1: bool = true && false;
    var and2: bool = true && true;
    var and3: bool = false && (1/0 == 1);    // Short circuiting

    var or1: bool = false || true;
    var or2: bool = false || false;
    var or3: bool = true || (1/0 == 1);   // Short circuiting

    var imp1: bool = true ==> true;
    var imp2: bool = true ==> false;
    var imp3: bool = false ==> (1/0 == 1);  // Short circuiting

    var impby1: bool = true <== true;
    var impby2: bool = false <== true;
    var impby3: bool = (1/0) == 1 <== false;   // Short circuiting

    var iff1: bool = true <==> true;
    var iff2: bool = true <==> false;

    var imp_right_assoc: bool = false ==> false ==> false;
    var imp_brackets:    bool = (false ==> false) ==> false;

    Test.print_i32(bit_and);
    Test.print_u32(bit_or);
    Test.print_u8(bit_xor);

    Test.print_i64(complex);
    Test.print_i8(negative);

    Test.print_i32(shl);
    Test.print_i8(shr);
    Test.print_i32(shr_neg);
    Test.print_u16(shr_u);

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
}
