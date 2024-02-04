module Arith

import Test;

interface {

// Compile-time evaluation of arithmetic operations.

const x: i32 = 1 + 3;
const y: i32 = 6 - 11;
const z: i32 = (10 + 1) - (3 + 5);

// Confusion of (subtract) (literal 1) with (literal -1)
const minus_no_space: i32 = 7 -1;

const big_plus: i64  = 10000000000 + 9000000000;
const big_minus: i64 = 10000000000 - 9000000000;
const unsigned_minus: u64 = u64(10000000000) - u64(9000000000);

const mul8:  i8  = i8(-10) * i8(5);
const mul16: i16 = i16(300) * i16(40);
const mul32: u32 = u32(100000) * u32(222);
const mul64: i64 = i64(200000000) * i64(1000);

const mul8_reg: i8 = i8(-9 - 1) * i8(4 + 1);
const mul16_reg: i16 = i16(299 + 1) * i16(39 + 1);
const mul32_reg: u32 = u32(100000 + 0) * u32(222 + 0);
const mul64_reg: i64 = i64(200000000 + 0) * i64(1000 + 0);

const sdiv1: i32 = 1000 / 13;
const smod1: i32 = 1000 % 13;
const sdiv2: i16 = i16(-1000) / i16(-13);
const smod2: i16 = i16(-1000) % i16(-13);
const sdiv3: i32 = 1000 / -13;
const smod3: i32 = 1000 % -13;
const sdiv4: i64 = i64(-1000) / i64(13);
const smod4: i64 = i64(-1000) % i64(13);

const sdiv5: i8 = i8(100) / i8(-13);
const smod5: i8 = i8(100) % i8(-13);
const sdiv6: i8 = i8(-100) / i8(13);
const smod6: i8 = i8(-100) % i8(13);

const udiv8: u8 = u8(200) / u8(13);
const umod8: u8 = u8(200) % u8(13);
const udiv: u32 = u32(1000) / u32(13);
const umod: u32 = u32(1000) % u32(13);

const negate: i32 = - (22 + 33);

function main()
{
    Test.print_i32(x);
    Test.print_i32(y);
    Test.print_i32(z);

    Test.print_i32(minus_no_space);

    Test.print_i64(big_plus);
    Test.print_i64(big_minus);
    Test.print_i64(unsigned_minus);

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
}

}
