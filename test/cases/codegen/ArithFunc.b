module ArithFunc

import Test;

interface {

// Similar to Arith.b and BinopImplicitCast.b,
// except that the operators are executed inside a function.
// This tests runtime codegen (as opposed to compile-time evaluation
// of expressions).

function main()
{
    var x: i32 = 1 + 3;
    var y: i32 = 6 - 11;
    var z: i32 = (10 + 1) - (3 + 5);

    // Confusion of (subtract) (literal 1) with (literal -1)
    var minus_no_space: i32 = 7 -1;

    var big_plus: i64  = 10000000000 + 9000000000;
    var big_minus: i64 = 10000000000 - 9000000000;

    var mul8:  i8  = i8(-10) * i8(5);
    var mul16: i16 = i16(300) * i16(40);
    var mul32: u32 = u32(100000) * u32(222);
    var mul64: i64 = i64(200000000) * i64(1000);

    var mul8_reg: i8 = i8(-9 - 1) * i8(4 + 1);
    var mul16_reg: i16 = i16(299 + 1) * i16(39 + 1);
    var mul32_reg: u32 = u32(100000 + 0) * u32(222 + 0);
    var mul64_reg: i64 = i64(200000000 + 0) * i64(1000 + 0);

    var sdiv1: i32 = 1000 / 13;
    var smod1: i32 = 1000 % 13;
    var sdiv2: i16 = i16(-1000) / i16(-13);
    var smod2: i16 = i16(-1000) % i16(-13);
    var sdiv3: i32 = 1000 / -13;
    var smod3: i32 = 1000 % -13;
    var sdiv4: i64 = i64(-1000) / i64(13);
    var smod4: i64 = i64(-1000) % i64(13);

    var sdiv5: i8 = i8(100) / i8(-13);
    var smod5: i8 = i8(100) % i8(-13);
    var sdiv6: i8 = i8(-100) / i8(13);
    var smod6: i8 = i8(-100) % i8(13);

    var udiv8: u8 = u8(200) / u8(13);
    var umod8: u8 = u8(200) % u8(13);
    var udiv: u32 = u32(1000) / u32(13);
    var umod: u32 = u32(1000) % u32(13);

    var negate: i32 = - (22 + 33);

    Test.print_i32(x);
    Test.print_i32(y);
    Test.print_i32(z);

    Test.print_i32(minus_no_space);

    Test.print_i64(big_plus);
    Test.print_i64(big_minus);

    Test.print_i8(mul8);
    Test.print_i16(mul16);
    Test.print_u32(mul32);
    Test.print_i64(mul64);

    Test.print_i8(mul8_reg);
    Test.print_i16(mul16_reg);
    Test.print_u32(mul32_reg);
    Test.print_i64(mul64_reg);

    Test.print_i32(sdiv1);
    Test.print_i32(smod1);
    Test.print_i16(sdiv2);
    Test.print_i16(smod2);
    Test.print_i32(sdiv3);
    Test.print_i32(smod3);
    Test.print_i64(sdiv4);
    Test.print_i64(smod4);

    Test.print_i8(sdiv5);
    Test.print_i8(smod5);
    Test.print_i8(sdiv6);
    Test.print_i8(smod6);

    Test.print_u8(udiv8);
    Test.print_u8(umod8);
    Test.print_u32(udiv);
    Test.print_u32(umod);

    Test.print_i32(negate);

    var cast_to_signed: i64 = i64(-999) + u32(100);
    var cast_to_signed_2: i64 = i64(-999) + u32(4000000000);
    var cast_both: i32 = i8(1) + u16(65535);

    Test.print_i64(cast_to_signed);
    Test.print_i64(cast_to_signed_2);
    Test.print_i32(cast_both);
}

}
