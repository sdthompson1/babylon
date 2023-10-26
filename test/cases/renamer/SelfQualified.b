module SelfQualified

interface {
    function main();
}

import Test;

// Check that using a qualified name from the current module works
// (without an import statement)

const y: i32 = 100;
const z: i32 = SelfQualified.y + 20;

function main()
{
    Test.print_i32(y);
    Test.print_i32(z);
}
