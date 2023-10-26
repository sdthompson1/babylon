module Casts
interface {}
  const i8_at_max: i8 = i8(127);
  const i8_above_max: i8 = i8(128);
  const i8_at_min: i8 = i8(-128);
  const i8_below_min: i8 = i8(-129);

  const i16_at_max: i16 = i16(32767);
  const i16_above_max: i16 = i16(32768);
  const i16_at_min: i16 = i16(-32768);
  const i16_below_min: i16 = i16(-32769);

  const i32_at_min: i32 = i32(i64(-2147483648));
  const i32_at_max: i32 = i32(i64(2147483647));
  const i64_above_i32_max: i64 = i64(i32_at_max) + i64(1);
  const i64_below_i32_min: i64 = i64(i32_at_min) - i64(1);
  const i32_above_max: i32 = i32(i64_above_i32_max);
  const i32_below_min: i32 = i32(i64_below_i32_min);

  const i64_at_min: i64 = i64(-9223372036854775808);
  const i64_at_max: i64 = i64(9223372036854775807);
  const i64_above_max: i64 = i64(9223372036854775808);

  const u8_negative: u8 = u8(-1);
  const u8_zero: u8 = u8(0);
  const u8_at_max: u8 = u8(255);
  const u8_above_max: u8 = u8(256);

  const u16_negative: u16 = u16(-1);
  const u16_zero: u16 = u16(0);
  const u16_at_max: u16 = u16(65535);
  const u16_above_max: u16 = u16(65536);

  const u32_negative: u32 = u32(-1);
  const u32_zero: u32 = u32(0);
  const u32_at_max: u32 = u32(4294967295);
  const u32_above_max: u32 = u32(4294967296);

  const u64_negative: u64 = u64(-1);
  const u64_zero: u64 = u64(0);
  const u64_at_max: u64 = u64(18446744073709551615);
