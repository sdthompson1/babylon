module MatchArmCoerce

// In a match expression, each arm after the first is implicitly
// converted to the type of the first arm. If the conversion is a
// narrowing one, the verifier must prove that it cannot fail.

interface {}

datatype ABC = A | B | C;


// Integer conversions

function widening(c: ABC, x: i64, y: i32): i64
{
    return match c { case A => x  case _ => y };   // OK, i32 to i64 cannot fail
}

function narrowing_unknown(c: ABC, x: i32, y: i64): i32
{
    return match c { case A => x  case _ => y };   // Error, y might not fit in i32
}

function narrowing_fits(c: ABC, x: i32, y: i64): i32
    requires i64(-100) <= y && y <= i64(100);
{
    return match c { case A => x  case _ => y };   // OK
}

function narrowing_constants(c: ABC, x: i8): i8
{
    var v1 = match c { case A => x  case B => 127  case C => -128 };   // OK
    var v2 = match c { case A => x  case B => 128  case C => 0 };      // Error, 128 doesn't fit in i8
    var v3 = match c { case A => x  case B => 0  case C => -129 };     // Error, -129 doesn't fit in i8
    return v1;
}

function narrowing_arm_not_taken(c: ABC, x: i32, y: i64): i32
    requires c == A;
{
    // OK, the conversion only has to succeed if the arm is taken
    return match c { case A => x  case _ => y };
}

function narrowing_arm_taken(c: ABC, x: i32, y: i64): i32
    requires c == B;
    requires y == i64(3000000000);
{
    return match c { case A => x  case _ => y };   // Error, y doesn't fit in i32
}

function signed_to_unsigned(c: ABC, x: u8, y: i32): u8
    requires y >= 0;
{
    return match c { case A => x  case _ => y };   // Error, y might be greater than 255
}

function first_arm_decides(c: ABC, x: i32, y: i64): i64
{
    // OK, the arms are converted to i64 here (not i32)
    return match c { case A => y  case _ => x };
}


// Array conversions

function to_incomplete(c: ABC, ref r: i32[], ref s: i32[10], ref t: i32[*]): u64
{
    return sizeof(match c { case A => r  case B => s  case C => t });   // OK, cannot fail
}

function to_fixed_unknown(c: bool, ref r: i32[10], ref s: i32[]): u64
{
    return sizeof(match c { case true => r  case false => s });   // Error, s might have the wrong size
}

function to_fixed_correct_size(c: bool, ref r: i32[10], ref s: i32[]): u64
    requires sizeof(s) == u64(10);
    ensures return == u64(10);
{
    return sizeof(match c { case true => r  case false => s });   // OK
}

function to_fixed_from_allocatable(c: bool, ref r: i32[10], ref s: i32[*]): u64
    requires sizeof(s) == u64(10);
{
    return sizeof(match c { case true => r  case false => s });   // OK
}

function to_fixed_wrong_size(c: bool, ref r: i32[10], ref s: i32[*]): u64
    requires sizeof(s) == u64(11);
{
    return sizeof(match c { case true => r  case false => s });   // Error, s has the wrong size
}
