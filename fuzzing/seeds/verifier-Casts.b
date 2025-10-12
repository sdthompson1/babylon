module Main
interface {}

function f()
{
  var i8_at_max: i8 = i8(127);
  var i8_above_max: i8 = i8(128);
  var i8_at_min: i8 = i8(-128);
  var i8_below_min: i8 = i8(-129);

  var i16_at_max: i16 = i16(32767);
  var i16_above_max: i16 = i16(32768);
  var i16_at_min: i16 = i16(-32768);
  var i16_below_min: i16 = i16(-32769);

  var i32_at_min: i32 = i32(i64(-2147483648));
  var i32_at_max: i32 = i32(i64(2147483647));
  var i64_above_i32_max: i64 = i64(i32_at_max) + i64(1);
  var i64_below_i32_min: i64 = i64(i32_at_min) - i64(1);
  var i32_above_max: i32 = i32(i64_above_i32_max);
  var i32_below_min: i32 = i32(i64_below_i32_min);

  var i64_at_min: i64 = i64(-9223372036854775808);
  var i64_at_max: i64 = i64(9223372036854775807);
  var i64_above_max: i64 = i64(9223372036854775808);

  var u8_negative: u8 = u8(-1);
  var u8_zero: u8 = u8(0);
  var u8_at_max: u8 = u8(255);
  var u8_above_max: u8 = u8(256);

  var u16_negative: u16 = u16(-1);
  var u16_zero: u16 = u16(0);
  var u16_at_max: u16 = u16(65535);
  var u16_above_max: u16 = u16(65536);

  var u32_negative: u32 = u32(-1);
  var u32_zero: u32 = u32(0);
  var u32_at_max: u32 = u32(4294967295);
  var u32_above_max: u32 = u32(4294967296);

  var u64_negative: u64 = u64(-1);
  var u64_zero: u64 = u64(0);
  var u64_at_max: u64 = u64(18446744073709551615);
}
