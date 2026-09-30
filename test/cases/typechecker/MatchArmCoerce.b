module MatchArmCoerce

// The type of a match expression is the type of its first arm. Each
// later arm is implicitly converted to that type, using the same
// conversions as for function arguments (i.e. casts between the
// finite integer types, and casts between array types).

interface {}

datatype ABC = A | B | C;
datatype D = D(i32);
datatype Maybe<a> = Nothing | Just(a);

function take_i32(ref x: i32) {}
function take_i64(ref x: i64) {}


// Integer conversions

function widening(c: ABC, x: i64): i64
{
    var v = match c { case A => x  case B => 1  case C => i8(2) };   // OK, v :: i64
    take_i64(v);
    return v;
}

function narrowing(c: ABC, x: i32, y: i64): i32
{
    // OK (for the typechecker). The second arm is cast from i64 to i32;
    // the verifier will check that the value is in range.
    var v = match c { case A => x  case _ => y };    // v :: i32
    take_i32(v);
    return v;
}

function first_arm_decides(c: ABC, x: i32, y: i64)
{
    var v = match c { case A => y  case _ => x };    // v :: i64
    take_i32(v);     // Error, v is not i32 (and the result of a cast is not an lvalue)
    take_i64(v);     // OK

    // The expected type of the statement does not change this: the arms
    // are converted to i64, and then the result is converted to i32.
    var w: i32 = match c { case A => y  case _ => x };
    take_i32(w);     // OK
}

function signed_unsigned(c: ABC, x: u8, y: i32): u8
{
    return match c { case A => x  case B => y  case C => 100 };   // OK
}


// Array conversions

function array_to_incomplete(c: ABC, ref r: i32[], ref s: i32[10], ref t: i32[*]): u64
{
    return sizeof(match c { case A => r  case B => s  case C => t });   // OK, arms are i32[]
}

function array_same_type(c: bool, ref r: i32[10], ref s: i32[10]): u64
{
    return sizeof(match c { case true => r  case false => s });   // OK
}

function array_to_fixed(c: ABC, ref r: i32[10], ref s: i32[*], ref t: i32[]): u64
{
    // OK (for the typechecker). The second and third arms are cast to i32[10];
    // the verifier will check that they have the correct size.
    return sizeof(match c { case A => r  case B => s  case C => t });
}

ghost function fixed_to_allocatable(c: bool, r: i32[*], s: i32[10]): u64
{
    return sizeof(match c { case true => r  case false => s });   // Error, can't convert i32[10] to i32[*]
}

ghost function incomplete_to_allocatable(c: bool, r: i32[*], s: i32[]): u64
{
    return sizeof(match c { case true => r  case false => s });   // Error, can't convert i32[] to i32[*]
}

ghost function array_wrong_size(c: bool, r: i32[10], s: i32[20]): u64
{
    return sizeof(match c { case true => r  case false => s });   // Error, can't convert i32[20] to i32[10]
}

ghost function array_element_type(c: bool, r: i32[], s: i64[]): u64
{
    return sizeof(match c { case true => r  case false => s });   // Error, element types differ
}


// No other conversions

function bool_vs_int(c: ABC): bool
{
    return match c { case A => true  case B => 1  case C => false };   // Error, 1 is not bool
}

function int_vs_bool(c: ABC): i32
{
    return match c { case A => 1  case B => true  case C => 2 };   // Error, true is not i32
}

function record_vs_datatype(c: bool): i32
{
    var v = match c { case true => {x = 1}  case false => D(1) };   // Error, D is not a record
    return 0;
}

function inside_datatype(c: bool, x: i64, y: i32)
{
    // Conversions apply to the arm itself, not to parts of it.
    var v = match c { case true => Just(x)  case false => Just(y) };   // Error, Maybe<i32> is not Maybe<i64>
}

function inside_record(c: bool, x: i64, y: i32)
{
    var v = match c { case true => {x, x}  case false => {x, y} };   // Error
}

function several_errors(c: ABC, x: i64)
{
    // Each arm is compared with the first arm.
    var v = match c {
        case A => x
        case B => true      // Error
        case C => D(1)      // Error
    };
}


// Arms of the same type after unification (no conversion is needed)

function unified(c: ABC): Maybe<i32>
{
    var v = match c { case A => Nothing  case B => Just(1)  case C => Nothing };   // OK, v :: Maybe<i32>
    return v;
}

function not_determined(c: ABC)
{
    var v = match c { case A => Nothing  case B => Nothing  case C => Nothing };   // Error, unable to infer type
}
