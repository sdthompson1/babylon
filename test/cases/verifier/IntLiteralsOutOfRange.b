module IntLiteralsOutOfRange
interface {}
  const i64_above_max: i64 = 9223372036854775808;    // Verif error (u64 constant, implicit cast to i64) - line 3

  const i32_below_min: i32 = -2147483649;    // Verif error (i64 constant, implicit cast to i32) - line 5
  const i32_min:       i32 = -2147483648;
  const i32_max:       i32 = 2147483647;
  const i32_above_max: i32 = 2147483648;     // Verif error - line 8

  const i16_below_min: i16 = -32769;   // Verif error - line 10
  const i16_min:       i16 = -32768;
  const i16_max:       i16 = 32767;
  const i16_above_max: i16 = 32768;    // Verif error - line 13

  const i8_below_min:  i8 = -129;   // Verif error - line 15
  const i8_min:        i8 = -128;
  const i8_max:        i8 = 127;
  const i8_above_max:  i8 = 128;    // Verif error - line 18

  const u64_negative:  u64 = -1;                      // Verifier error - line 20
  const u64_max:       u64 = 18446744073709551615;

  const u32_negative:  u32 = -1;             // Verifier error - line 23
  const u32_max:       u32 = 4294967295;
  const u32_above_max: u32 = 4294967296;     // Verifier error - line 25

  const u16_negative:  u16 = -1;     // Verif error - line 27
  const u16_max:       u16 = 65535;
  const u16_above_max: u16 = 65536;  // Verif error - line 29

  const u8_negative:   u8 = -1;      // Verif error - line 31
  const u8_max:        u8 = 255;
  const u8_above_max:  u8 = 256;     // Verif error - line 33
