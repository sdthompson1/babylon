module Casts
interface { function main(); }

// Testing integer casts

import Test;

const i8_plus:   i8  = i8(100);
const i8_minus:  i8  = i8(-50);
const i8_min:    i8  = i8(-128);
const i8_max:    i8  = i8(127);

const i16_from_u8: i16 = i16(u8(200));
const i16_small_plus: i16 = i16(i8(123));
const i16_plus:  i16 = i16(12345);
const i16_small_minus: i16 = i16(-123);
const i16_minus: i16 = i16(-12345);

const i32_plus:  i32 = i32(123456789);
const i32_minus: i32 = i32(-123456789);

const i64_small_plus: i64 = i64(999);
const i64_plus:  i64 = i64(1234567890123456789);
const i64_small_minus: i64 = i64(-999);
const i64_minus: i64 = i64(-1234567890123456789);

const i8_calc_plus:   i8  = i8(100 + 20);
const i8_calc_minus:  i8  = i8(-100 - 20);

const i8_to_i8_plus:   i8  = i8(i8(1 + 2));
const i8_to_i8_minus:  i8  = i8(i8(1 - 2));
const i8_to_i16_plus:  i16 = i16(i8(1 + 2));
const i8_to_i16_minus: i16 = i16(i8(1 - 2));
const i8_to_i32_plus:  i32 = i32(i8(100 + 1));
const i8_to_i32_minus: i32 = i32(i8(-100 - 1));
const i8_to_i64_plus:  i64 = i64(i8(100 + 1));
const i8_to_i64_minus: i64 = i64(i8(-100 - 1));

const i16_to_i8_plus:   i8  = i8(i16(1 + 2));
const i16_to_i8_minus:  i8  = i8(i16(1 - 2));
const i16_to_i16_plus:  i16 = i16(i16(1 + 2));
const i16_to_i16_minus: i16 = i16(i16(1 - 2));
const i16_to_i32_plus:  i32 = i32(i16(100 + 1));
const i16_to_i32_minus: i32 = i32(i16(-100 - 1));
const i16_to_i64_plus:  i64 = i64(i16(100 + 1));
const i16_to_i64_minus: i64 = i64(i16(-100 - 1));

const i32_to_i8_plus:   i8 = i8(i32(100 + 1));
const i32_to_i8_minus:  i8 = i8(i32(1 - 2));
const i32_to_i64_plus:  i64 = i64(i32(100 + 1));
const i32_to_i64_minus: i64 = i64(i32(-100 - 1));

const u8_plus:   u8  = u8(200);
const u16_plus:  u16 = u16(65500);
const u32_plus:  u32 = u32(4000000000);
const u64_plus:  u64 = u64(4000000000000);

const u8_calc:    u8  = u8 (100 + 140);
const u16_calc:   u16 = u16(10000 + 30000);
const u32_calc:   u32 = u32(1000000 + 3000000);
const u64_calc:   u64 = u64(1000000 + 3000000);
const u64_calc_2: u64 = u64(999999999999 + i64(1));

const u8_to_u16:  u16 = u16(u8(1 + 2));
const u8_to_u32:  u32 = u32(u8(100 + 1));
const u8_to_u64:  u64 = u64(u8(100 + 1));
const u16_to_u32: u32 = u32(u16(100 + 1));
const u16_to_u64: u64 = u64(u16(100 + 1));
const u32_to_u64: u64 = u64(u32(100 + 1));

const u64_to_u32: u32 = u32(u64(99 + 99));

function main()
{
    Test.print_i8( i8_plus );
    Test.print_i8( i8_minus );
    Test.print_i8( i8_min );
    Test.print_i8( i8_max );

    Test.print_i16( i16_from_u8 );
    Test.print_i16( i16_small_plus );
    Test.print_i16( i16_plus );
    Test.print_i16( i16_small_minus );
    Test.print_i16( i16_minus );
  
    Test.print_i32( i32_plus );
    Test.print_i32( i32_minus );

    Test.print_i64( i64_small_plus );
    Test.print_i64( i64_plus );
    Test.print_i64( i64_small_minus );
    Test.print_i64( i64_minus );

    Test.print_i8( i8_calc_plus );
    Test.print_i8( i8_calc_minus );

    Test.print_i8( i8_to_i8_plus );
    Test.print_i8( i8_to_i8_minus );
    Test.print_i16( i8_to_i16_plus );
    Test.print_i16( i8_to_i16_minus );
    Test.print_i32( i8_to_i32_plus );
    Test.print_i32( i8_to_i32_minus );
    Test.print_i64( i8_to_i64_plus );
    Test.print_i64( i8_to_i64_minus );

    Test.print_i8( i16_to_i8_plus );
    Test.print_i8( i16_to_i8_minus );
    Test.print_i16( i16_to_i16_plus );
    Test.print_i16( i16_to_i16_minus );
    Test.print_i32( i16_to_i32_plus );
    Test.print_i32( i16_to_i32_minus );
    Test.print_i64( i16_to_i64_plus );
    Test.print_i64( i16_to_i64_minus );

    Test.print_i8( i32_to_i8_plus );
    Test.print_i8( i32_to_i8_minus );
    Test.print_i64( i32_to_i64_plus );
    Test.print_i64( i32_to_i64_minus );

    Test.print_u8( u8_plus );
    Test.print_u16( u16_plus );
    Test.print_u32( u32_plus );
    Test.print_u64( u64_plus );

    Test.print_u8( u8_calc );
    Test.print_u16( u16_calc );
    Test.print_u32( u32_calc );
    Test.print_u64( u64_calc );
    Test.print_u64( u64_calc_2 );

    Test.print_u16( u8_to_u16  );
    Test.print_u32( u8_to_u32  );
    Test.print_u64( u8_to_u64  );
    Test.print_u32( u16_to_u32 );
    Test.print_u64( u16_to_u64 );
    Test.print_u64( u32_to_u64 );
    Test.print_u32( u64_to_u32 );
}
