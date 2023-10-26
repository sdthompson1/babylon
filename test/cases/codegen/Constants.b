module Constants
interface { function main(); }

// Just printing some simple constant integer values

import Test;

function main()
{
    Test.print_i32( 100 );
    Test.print_i32( -24 );
    Test.print_i32( 0 );
    Test.print_i32( 2147483647 );     // Max possible i32
    Test.print_i32( -2147483648 );    // Min possible i32
    Test.print_bool( true );
    Test.print_bool( false );
}