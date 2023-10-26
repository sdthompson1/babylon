module ConstantsIntImpl

  // Checking that an "exported" constant (i.e. declared in "interface"
  // but implemented separately) works

interface {
    const x: i32;
    function main();
}

import Test;

const x: i32 = 12345;

function main()
{
    Test.print_i32(x);
}
