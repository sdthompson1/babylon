module Main

// Let expressions

interface { function main(); }

import Test;

function main()
{
    Test.print_i32( let y = 1 in y + 1 );
    Test.print_i32( let y = (let y = 10 in y+5) in y+20 );
    Test.print_i32( let y = 10 in let z = 20 in y + z );
    Test.print_i32( let y = 10 in let y = 5 in 3*y );

    Test.print_i32(
        let a = 1 in let b = 2 in let c = 3 in let d = 4 in
        let e = 5 in let f = 6 in let g = 7 in let h = 8 in
        let i = 9 in let j = 10 in let k = 11 in let l = 12 in
        a+b+c+d+e+f+g+h+i+j+k+l
    );

    Test.print_i32( let a = 1 in let a = a + 2 in a );
}
