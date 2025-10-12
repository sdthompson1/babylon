module Main
interface {}
  // Various operator type errors:
  
  const x: i32 = 1 + true;
  const y: i32 = true + true;
  const z: i32 = (1 + true) + 2;
  const neg: i32 = - false;
  const complement: i32 = ~ false;
  const wrong_not: i32 = !0;    // not allowed, use the bool type instead
  const sh: i32 = 1 << false;
  const wrong_and: bool = true & false;  // not allowed, use && instead
  const negate_unsigned: u32 = - u32(1);

  const less: bool = 1 < true;
  const gtr_equal: bool = true >= false;
  const equal: bool = 1 == true;
  const not_equal: bool = true != 1;


  // Casts:

  // This is no longer a type error - it now casts to u64.
  const cast_to_u64: u64 = i32(1) + u64(2);

  // This is fine, there is a type that can represent all i64 and all u32 values (namely i64).
  const cast_to_signed: i64 = i64(1) + u32(2);

  // This is fine, we can "upgrade" both types to i32
  const cast_both: i32 = i8(1) + u16(65535);


  const c2: i32 = i32(true);   // Cast from bool not allowed
  const c3: i32 = i32(1 + true);    // Cast of something ill-typed


  // Logical operators:

  const iff: bool = 1 <==> 1;
  const ite1: i32 = if 1 then 2 else 3;
  const ite2: i32 = if 1 < 2 then 3 else false;
  const and_bad: bool = 1 && true;
  const or_bad: bool = false || 2;
  const imp_bad: bool = 1 ==> 2;
  const imp_by_bad: bool = 2 <== 1;


  // Misc:
  const shift_lhs_not_int: i32 = true << 1;
  const unop_bad_term: i32 = - (true + 1);

  ghost function equality_type_mismatch(): bool
  {
      return {1} == {1,2};   // Type error: Different tuple sizes.
  }
