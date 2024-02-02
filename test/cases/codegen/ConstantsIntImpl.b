module ConstantsIntImpl

  // Checking that an "exported" constant (i.e. declared in "interface"
  // but implemented separately) works

interface {
    const x: i32;
    const t: {i32, i32};
    function main();
}

import Test;

const x: i32 = 12345;
const t: {i32, i32} = {100, 200};

function main()
{
    Test.print_i32(x);
    Test.print_i32(t.0);
    Test.print_i32(t.1);
}
