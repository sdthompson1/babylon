module Generic

// Codegen for generic functions

interface { function main(); }

import Test;

function id<a>(x: a): a
    requires !allocated(x);
{
    return x;
}

const c8: i8 = 100;
const c16: i16 = 1000;
const c32: i32 = 1000;
const c64: i64 = 1000;

function main()
{
    Test.print_i8( id<i8>(c8) );
    Test.print_i16( id<i16>(c16) );
    Test.print_i32( id<i32>(c32) );
    Test.print_i64( id<i64>(c64) );
    Test.print_bool( id<bool>(true) );
    Test.print_i8( id<i8>(c8) + i8(10) );
}
