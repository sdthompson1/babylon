module Datatypes2

// More datatype tests (codegen)

interface { function main(); }

import Test;

datatype VarInt = I64(i64) | I32(i32) | I16(i16) | I8(i8);

function f(v: VarInt): i64
{
    match (v) {
        case I64(x) => return x;
        case I32(x) => return i64(x);
        case I16(x) => return i64(x);
        case I8(x)  => return i64(x);
    }
}


// Datatype with >256 variants (requires 2-byte tag)
datatype Big = XA0 | XA1 | XA2 | XA3 | XA4 | XA5 | XA6 | XA7
             | XB0 | XB1 | XB2 | XB3 | XB4 | XB5 | XB6 | XB7
             | XC0 | XC1 | XC2 | XC3 | XC4 | XC5 | XC6 | XC7
             | XD0 | XD1 | XD2 | XD3 | XD4 | XD5 | XD6 | XD7
             | XE0 | XE1 | XE2 | XE3 | XE4 | XE5 | XE6 | XE7
             | XF0 | XF1 | XF2 | XF3 | XF4 | XF5 | XF6 | XF7
             | XG0 | XG1 | XG2 | XG3 | XG4 | XG5 | XG6 | XG7
             | XH0 | XH1 | XH2 | XH3 | XH4 | XH5 | XH6 | XH7
             | XI0 | XI1 | XI2 | XI3 | XI4 | XI5 | XI6 | XI7
             | XJ0 | XJ1 | XJ2 | XJ3 | XJ4 | XJ5 | XJ6 | XJ7
             | XK0 | XK1 | XK2 | XK3 | XK4 | XK5 | XK6 | XK7
             | XL0 | XL1 | XL2 | XL3 | XL4 | XL5 | XL6 | XL7
             | XM0 | XM1 | XM2 | XM3 | XM4 | XM5 | XM6 | XM7
             | XN0 | XN1 | XN2 | XN3 | XN4 | XN5 | XN6 | XN7
             | XO0 | XO1 | XO2 | XO3 | XO4 | XO5 | XO6 | XO7
             | XP0 | XP1 | XP2 | XP3 | XP4 | XP5 | XP6 | XP7
             | XQ0 | XQ1 | XQ2 | XQ3 | XQ4 | XQ5 | XQ6 | XQ7
             | XR0 | XR1 | XR2 | XR3 | XR4 | XR5 | XR6 | XR7
             | XS0 | XS1 | XS2 | XS3 | XS4 | XS5 | XS6 | XS7
             | XT0 | XT1 | XT2 | XT3 | XT4 | XT5 | XT6 | XT7
             | XU0  | XU1  | XU2  | XU3  | XU4  | XU5  | XU6  | XU7
             | XV0  | XV1  | XV2  | XV3  | XV4  | XV5  | XV6  | XV7
             | XW0  | XW1  | XW2  | XW3  | XW4  | XW5  | XW6  | XW7
             | XX0  | XX1  | XX2  | XX3  | XX4  | XX5  | XX6  | XX7
             | XY0  | XY1  | XY2  | XY3  | XY4  | XY5  | XY6  | XY7
             | XZ0  | XZ1  | XZ2  | XZ3  | XZ4  | XZ5  | XZ6  | XZ7
             | XAA0 | XAA1 | XAA2 | XAA3 | XAA4 | XAA5 | XAA6 | XAA7
             | XAB0 | XAB1 | XAB2 | XAB3 | XAB4 | XAB5 | XAB6 | XAB7
             | XAC0 | XAC1 | XAC2 | XAC3 | XAC4 | XAC5 | XAC6 | XAC7
             | XAD0 | XAD1 | XAD2 | XAD3 | XAD4 | XAD5 | XAD6 | XAD7
             | XAE0 | XAE1 | XAE2 | XAE3 | XAE4 | XAE5 | XAE6 | XAE7
             | XAF0 | XAF1 | XAF2 | XAF3 | XAF4 | XAF5 | XAF6 | XAF7
             | XFinal (i32);

function f1(): i32
{
    var big: Big = XFinal(999);
    match big {
        case XFinal(i) => return i+1;
    }
}


// Store variant into subfield of a struct
function f2(): i32
{
    var v: {{VarInt,i32},i32} = {{I32(1),2},3};
    v.0.0 = I32(1);
    return (match (v.0.0) { case I32(x) => x + 1 } );
}


function main()
{
    Test.print_i64( f(I16(12321)) );
    Test.print_i32( f1() );
    Test.print_i32( f2() );
}
