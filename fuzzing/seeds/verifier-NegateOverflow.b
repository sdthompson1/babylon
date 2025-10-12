module Main
interface {}

function f()
{
  var neg32_ok:  i32 = - (1);
  var neg32_bad: i32 = - (-2147483648);

  var neg64_ok:  i64 = - i64(1000);
  var neg64_bad: i64 = - i64(-9223372036854775808);

  var neg16_ok:  i16 = - i16(-32767);
  var neg16_bad: i16 = - i16(-32768);

  var neg8_ok:   i8  = - i8(-127);
  var neg8_bad:  i8  = - i8(-128);
}
