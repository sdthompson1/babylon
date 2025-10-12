module Main
interface {}

function f()
{
  var i64_above_max: i64 = 9223372036854775808;    // Verif error (u64 constant, implicit cast to i64)

  var i32_below_min: i32 = -2147483649;    // Verif error (i64 constant, implicit cast to i32)
  var i32_min:       i32 = -2147483648;
  var i32_max:       i32 = 2147483647;
  var i32_above_max: i32 = 2147483648;     // Verif error - line 8

  var i16_below_min: i16 = -32769;   // Verif error - line 10
  var i16_min:       i16 = -32768;
  var i16_max:       i16 = 32767;
  var i16_above_max: i16 = 32768;    // Verif error - line 13

  var i8_below_min:  i8 = -129;   // Verif error - line 15
  var i8_min:        i8 = -128;
  var i8_max:        i8 = 127;
  var i8_above_max:  i8 = 128;    // Verif error - line 18

  var u64_negative:  u64 = -1;                      // Verifier error - line 20
  var u64_max:       u64 = 18446744073709551615;

  var u32_negative:  u32 = -1;             // Verifier error - line 23
  var u32_max:       u32 = 4294967295;
  var u32_above_max: u32 = 4294967296;     // Verifier error - line 25

  var u16_negative:  u16 = -1;     // Verif error - line 27
  var u16_max:       u16 = 65535;
  var u16_above_max: u16 = 65536;  // Verif error - line 29

  var u8_negative:   u8 = -1;      // Verif error - line 31
  var u8_max:        u8 = 255;
  var u8_above_max:  u8 = 256;     // Verif error - line 33
}
