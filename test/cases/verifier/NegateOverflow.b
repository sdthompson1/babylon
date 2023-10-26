module NegateOverflow
interface {}
  const neg32_ok:  i32 = - (1);
  const neg32_bad: i32 = - (-2147483648);

  const neg64_ok:  i64 = - i64(1000);
  const neg64_bad: i64 = - i64(-9223372036854775808);

  const neg16_ok:  i16 = - i16(-32767);
  const neg16_bad: i16 = - i16(-32768);

  const neg8_ok:   i8  = - i8(-127);
  const neg8_bad:  i8  = - i8(-128);
