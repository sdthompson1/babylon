module Division
interface {}

function f()
{
  var div_ok: i32 = 123456 / 17;
  var div_by_zero: i32 = 123456 / 0;

  var div_ok_i8:        i8  = i8(-127) / i8(-1);
  var div_overflow_i8:  i8  = i8(-128) / i8(-1);
  var div_ok_i16:       i16 = i16(-32767) / i16(-1);
  var div_overflow_i16: i16 = i16(-32768) / i16(-1);

  var div_ok_unsigned:      u32 = u32(123456) / u32(100);
  var div_by_zero_unsigned: u32 = u16(188) / u16(0);


  var mod_ok: i32 = 123456 % 17;
  var mod_by_zero: i32 = 123456 % 0;

  // Note: Technically INT_MIN % -1 doesn't overflow (only INT_MIN / -1
  // does), but it's undefined behaviour in C, so we don't want to allow
  // it.
  var mod_ok_i8:        i8  = i8(-127) % i8(-1);
  var mod_overflow_i8:  i8  = i8(-128) % i8(-1);
  var mod_ok_i16:       i16 = i16(-32767) % i16(-1);
  var mod_overflow_i16: i16 = i16(-32768) % i16(-1);

  var mod_ok_unsigned: u32 = u32(123456) % u32(100);
  var mod_by_zero_unsigned: u32 = u16(188) % u16(0);
}
