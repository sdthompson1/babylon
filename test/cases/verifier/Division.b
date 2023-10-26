module Division
interface {}
  const div_ok: i32 = 123456 / 17;
  const div_by_zero: i32 = 123456 / 0;

  const div_ok_i8:        i8  = i8(-127) / i8(-1);
  const div_overflow_i8:  i8  = i8(-128) / i8(-1);
  const div_ok_i16:       i16 = i16(-32767) / i16(-1);
  const div_overflow_i16: i16 = i16(-32768) / i16(-1);

  const div_ok_unsigned:      u32 = u32(123456) / u32(100);
  const div_by_zero_unsigned: u32 = u16(188) / u16(0);


  const mod_ok: i32 = 123456 % 17;
  const mod_by_zero: i32 = 123456 % 0;

  // Note: Technically INT_MIN % -1 doesn't overflow (only INT_MIN / -1
  // does), but it's undefined behaviour in C, so we don't want to allow
  // it, in case we are compiling to C.
  const mod_ok_i8:        i8  = i8(-127) % i8(-1);
  const mod_overflow_i8:  i8  = i8(-128) % i8(-1);
  const mod_ok_i16:       i16 = i16(-32767) % i16(-1);
  const mod_overflow_i16: i16 = i16(-32768) % i16(-1);

  const mod_ok_unsigned: u32 = u32(123456) % u32(100);
  const mod_by_zero_unsigned: u32 = u16(188) % u16(0);
