// Integer literals within range of their target types. Shouldn't
// error and shouldn't change the value.

module Main

import Test;

interface {
  const i64_min:   i64 = -9223372036854775808;
  const i64_below: i64 = -2147483649;
  const i32_min:   i32 = -2147483648;
  const i32_zero:  i32 = 0;
  const i32_max:   i32 = 2147483647;
  const u32_above: u32 = 2147483648;
  const u32_max:   u32 = 4294967295;
  const i64_above: i64 = 4294967296;
  const i64_max:   i64 = 9223372036854775807;
  const u64_above: u64 = 9223372036854775808;
  const u64_max:   u64 = 18446744073709551615;

  function main()
  {
    Test.print_i64(i64_min);
    Test.print_i64(i64_below);
    Test.print_i32(i32_min);
    Test.print_i32(i32_zero);
    Test.print_i32(i32_max);
    Test.print_u32(u32_above);
    Test.print_u32(u32_max);
    Test.print_i64(i64_above);
    Test.print_i64(i64_max);
    Test.print_u64(u64_above);
    Test.print_u64(u64_max);
  }
}
