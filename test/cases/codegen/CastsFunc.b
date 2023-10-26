module CastsFunc
interface { function main(); }

// Testing integer casts (at runtime)

import Test;

function main()
{
    var i8_plus:   i8  = i8(100);
    var i8_minus:  i8  = i8(-50);
    var i8_min:    i8  = i8(-128);
    var i8_max:    i8  = i8(127);

    var i16_from_u8: i16 = i16(u8(200));
    var i16_small_plus: i16 = i16(i8(123));
    var i16_plus:  i16 = i16(12345);
    var i16_small_minus: i16 = i16(-123);
    var i16_minus: i16 = i16(-12345);

    var i32_plus:  i32 = i32(123456789);
    var i32_minus: i32 = i32(-123456789);

    var i64_small_plus: i64 = i64(999);
    var i64_plus:  i64 = i64(1234567890123456789);
    var i64_small_minus: i64 = i64(-999);
    var i64_minus: i64 = i64(-1234567890123456789);

    var i8_calc_plus:   i8  = i8(100 + 20);
    var i8_calc_minus:  i8  = i8(-100 - 20);

    var i8_to_i8_plus:   i8  = i8(i8(1 + 2));
    var i8_to_i8_minus:  i8  = i8(i8(1 - 2));
    var i8_to_i16_plus:  i16 = i16(i8(1 + 2));
    var i8_to_i16_minus: i16 = i16(i8(1 - 2));
    var i8_to_i32_plus:  i32 = i32(i8(100 + 1));
    var i8_to_i32_minus: i32 = i32(i8(-100 - 1));
    var i8_to_i64_plus:  i64 = i64(i8(100 + 1));
    var i8_to_i64_minus: i64 = i64(i8(-100 - 1));

    var i16_to_i8_plus:   i8  = i8(i16(1 + 2));
    var i16_to_i8_minus:  i8  = i8(i16(1 - 2));
    var i16_to_i16_plus:  i16 = i16(i16(1 + 2));
    var i16_to_i16_minus: i16 = i16(i16(1 - 2));
    var i16_to_i32_plus:  i32 = i32(i16(100 + 1));
    var i16_to_i32_minus: i32 = i32(i16(-100 - 1));
    var i16_to_i64_plus:  i64 = i64(i16(100 + 1));
    var i16_to_i64_minus: i64 = i64(i16(-100 - 1));

    var i32_to_i8_plus:   i8 = i8(i32(100 + 1));
    var i32_to_i8_minus:  i8 = i8(i32(1 - 2));
    var i32_to_i64_plus:  i64 = i64(i32(100 + 1));
    var i32_to_i64_minus: i64 = i64(i32(-100 - 1));

    var u8_plus:   u8  = u8(200);
    var u16_plus:  u16 = u16(65500);
    var u32_plus:  u32 = u32(4000000000);
    var u64_plus:  u64 = u64(4000000000000);

    var u8_calc:    u8  = u8 (100 + 140);
    var u16_calc:   u16 = u16(10000 + 30000);
    var u32_calc:   u32 = u32(1000000 + 3000000);
    var u64_calc:   u64 = u64(1000000 + 3000000);
    var u64_calc_2: u64 = u64(999999999999 + i64(1));

    var u8_to_u16:  u16 = u16(u8(1 + 2));
    var u8_to_u32:  u32 = u32(u8(100 + 1));
    var u8_to_u64:  u64 = u64(u8(100 + 1));
    var u16_to_u32: u32 = u32(u16(100 + 1));
    var u16_to_u64: u64 = u64(u16(100 + 1));
    var u32_to_u64: u64 = u64(u32(100 + 1));

    var u64_to_u32: u32 = u32(u64(99 + 99));

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
