module BinopImplicitCast
interface { function main(); }

// Test binary operator implicit type-widening.

import Test;

// These are fine, there is a type that can represent all i64 and all u32 values (namely i64).
const cast_to_signed: i64 = i64(-999) + u32(100);
const cast_to_signed_2: i64 = i64(-999) + u32(4000000000);

// This is fine, we can "upgrade" both types to i32
const cast_both: i32 = i8(1) + u16(65535);

function main()
{
    Test.print_i64(cast_to_signed);
    Test.print_i64(cast_to_signed_2);
    Test.print_i32(cast_both);
}
