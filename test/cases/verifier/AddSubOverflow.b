module AddSubOverflow
interface {}
  const add_ok:  i32 = 1 + 1;
  const add_bad: i32 = 2000000000 + 1000000000;

  const add_neg_ok:  i32 = 1 + -1;
  const add_neg_bad: i32 = -2147483640 + -9;

  const add_unsigned_bad: u32 = 2147483648 + 2147483648;

  const sub_ok:  i32 = 1 - 1;
  const sub_bad: i32 = -2000000000 - 1000000000;

  const sub_neg_ok: i32 = 1 - -1;
  const sub_neg_bad: i32 = 2000000000 - -1000000000;

  const sub_unsigned_bad: u32 = 2147483648 - 2147483649;
