module AddSubOverflow
interface {}

function f1()
{
  var add_ok:  i32 = 1 + 1;
  var add_bad: i32 = 2000000000 + 1000000000;

  var add_neg_ok:  i32 = 1 + -1;
  var add_neg_bad: i32 = -2147483640 + -9;

  var add_unsigned_bad: u32 = 2147483648 + 2147483648;

  var sub_ok:  i32 = 1 - 1;
  var sub_bad: i32 = -2000000000 - 1000000000;

  var sub_neg_ok: i32 = 1 - -1;
  var sub_neg_bad: i32 = 2000000000 - -1000000000;

  var sub_unsigned_bad: u32 = 2147483648 - 2147483649;

  // u64 + i32 is taken to be u64, so this will be an error:
  var add_u64_i32_bad = u64(10) + i32(-11);
}
