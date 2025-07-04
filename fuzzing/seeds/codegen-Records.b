module Records

// Record code generation

interface { function main(); }
import Test;

const r = { x = 1, y = 2 };
  
const s = {{{ r with y = 3 } with x = 4 } with };

function main()
{
    Test.print_i32( r.x );
    Test.print_i32( r.y );
    Test.print_i32( s.x );
    Test.print_i32( s.y );
    Test.print_i32( {{x=true, y=10} with y=98+2} . y );
}
