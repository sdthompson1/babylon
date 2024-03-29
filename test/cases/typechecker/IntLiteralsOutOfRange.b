module IntLiteralsOutOfRange
interface {

  const i64_below_min: i64 = -9223372036854775809;    // Type error (too low for any type)
  const i64_min:       i64 = -9223372036854775808;    // No error
  const i64_max:       i64 =  9223372036854775807;    // No error
  const i64_above_max: i64 =  9223372036854775808;    // Compile time error (implicit cast u64 to i64, which fails)

  const silly: u64 = 999999999999999999999999999999999999999999999999999999999999999999999999999999999999999;

}
