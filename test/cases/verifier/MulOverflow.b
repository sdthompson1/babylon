module MulOverflow
interface {}
  const mul_ok:  i32 = 2 * 3;
  const add_bad: i32 = 100000 * 200000;

  const mul_neg_ok:  i32 = 2 * -3;
  const mul_neg_bad: i32 = -100000 * -200000;
  const mul_neg_bad_2: i32 = -100000 * 256789;

  const mul_unsigned_ok: u32 = 1000 * 3000;
  const mul_unsigned_bad: u32 = 100000 * 200000;

  const mul_i8_bad: i8 = i8(100) * i8(2);
  const mul_u8_bad: u8 = u8(100) * u8(3);
