module MulOverflow
interface {}

function f()
{
  var mul_ok:  i32 = 2 * 3;
  var add_bad: i32 = 100000 * 200000;

  var mul_neg_ok:  i32 = 2 * -3;
  var mul_neg_bad: i32 = -100000 * -200000;
  var mul_neg_bad_2: i32 = -100000 * 256789;

  var mul_unsigned_ok: u32 = u32(1000) * u32(3000);
  var mul_unsigned_bad: u32 = u32(100000) * u32(200000);

  var mul_i8_bad: i8 = i8(100) * i8(2);
  var mul_u8_bad: u8 = u8(100) * u8(3);
}
