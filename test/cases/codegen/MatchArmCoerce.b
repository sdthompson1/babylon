module MatchArmCoerce

// In a match expression, each arm after the first is implicitly
// converted to the type of the first arm. This test checks that
// such expressions compile and run correctly.

interface {
    function main();
}

import Test;

datatype ABC = A | B | C;


// Integer conversions

function widen(c: ABC, x: i64, y: i32, z: i8): i64
{
    return match c { case A => x  case B => y  case C => z };
}

function narrow(c: ABC, x: i8, y: i32, z: i64): i8
    requires -100 <= y && y <= 100;
    requires i64(-100) <= z && z <= i64(100);
{
    return match c { case A => x  case B => y  case C => z };
}

function to_unsigned(c: ABC, x: u16, y: i32): u16
    requires 0 <= y && y <= 65535;
{
    return match c { case A => x  case B => y  case C => 65535 };
}

function to_signed(c: ABC, x: i64, y: u32): i64
{
    return match c { case A => x  case B => y  case C => -1 };
}


// Array conversions

function size_incomplete(c: ABC, ref r: i32[], ref s: i32[3], ref t: i32[*]): u64
{
    return sizeof(match c { case A => r  case B => s  case C => t });
}

function first_incomplete(c: ABC, ref r: i32[], ref s: i32[3], ref t: i32[*]): i32
    requires sizeof(r) > u64(0);
    requires sizeof(t) > u64(0);
{
    return (match c { case A => r  case B => s  case C => t })[0];
}

function last_fixed(c: ABC, ref r: i32[3], ref s: i32[], ref t: i32[*]): i32
    requires sizeof(s) == u64(3);
    requires sizeof(t) == u64(3);
{
    return (match c { case A => r  case B => s  case C => t })[2];
}


function main()
{
    // Widening (including sign extension)
    var w1 = widen(A, i64(5000000000), -2, i8(-3));
    print_i64(w1);
    var w2 = widen(B, i64(5000000000), -2, i8(-3));
    print_i64(w2);
    var w3 = widen(C, i64(5000000000), -2, i8(-3));
    print_i64(w3);

    // Narrowing
    var n1 = narrow(A, i8(-128), 99, i64(-99));
    print_i8(n1);
    var n2 = narrow(B, i8(-128), 99, i64(-99));
    print_i8(n2);
    var n3 = narrow(C, i8(-128), 99, i64(-99));
    print_i8(n3);

    // Signed to unsigned, and vice versa
    var u1 = to_unsigned(A, u16(1), 40000);
    print_u16(u1);
    var u2 = to_unsigned(B, u16(1), 40000);
    print_u16(u2);
    var u3 = to_unsigned(C, u16(1), 40000);
    print_u16(u3);

    var s1 = to_signed(A, i64(-5000000000), u32(4000000000));
    print_i64(s1);
    var s2 = to_signed(B, i64(-5000000000), u32(4000000000));
    print_i64(s2);
    var s3 = to_signed(C, i64(-5000000000), u32(4000000000));
    print_i64(s3);

    // Match expression used directly as an argument
    print_i64(match B { case A => i64(1)  case B => 2  case C => 3 });
    print_u8(match C { case A => u8(1)  case B => 2  case C => 255 });

    // Arrays
    var a: i32[5];
    a[0] = 10;
    var b: i32[3];
    b[0] = 20;
    b[2] = 22;
    var d: i32[*];
    alloc_array<i32>(d, 3);
    d[0] = 30;
    d[2] = 32;

    var z1 = size_incomplete(A, a, b, d);
    print_u64(z1);
    var z2 = size_incomplete(B, a, b, d);
    print_u64(z2);
    var z3 = size_incomplete(C, a, b, d);
    print_u64(z3);

    var f1 = first_incomplete(A, a, b, d);
    print_i32(f1);
    var f2 = first_incomplete(B, a, b, d);
    print_i32(f2);
    var f3 = first_incomplete(C, a, b, d);
    print_i32(f3);

    var e: i32[3];
    e[2] = 42;
    var l1 = last_fixed(A, e, b, d);
    print_i32(l1);
    var l2 = last_fixed(B, e, b, d);
    print_i32(l2);
    var l3 = last_fixed(C, e, b, d);
    print_i32(l3);

    free_array<i32>(d);
}
