module Bitwise
interface {}
  const shl_i8_bad: i8 = i8(1) << 7;
  const shl_u8_bad: u8 = u8(200) << 1;

  const shl8_too_many: i8 = i8(0) << 8;
  const shl32_ok: i32 = 0 << 8;
  const shl32_too_many: i32 = 0 << 32;
  const shr32_too_many: i32 = 0 >> 32;

  const shl64_ok: i64 = i64(1) << 31;
  const shl64_too_many: i64 = i64(1) << 63;    // 2^63, but 2^63 - 1 is the max possible

  const complex1: i32 = 0 >> (32 | 64);
  const complex2: i32 = (u8(64) | u8(32)) << 2;

  const cpl_u_ok:       u8 =  ~ u8(2) + u8(2);
  const cpl_u_overflow: u8 =  ~ u8(2) + u8(3);
  const cpl_i_ok:       i8 =  ~ i8(-126) + i8(2);
  const cpl_i_overflow: i8 =  ~ i8(-126) + i8(3);
