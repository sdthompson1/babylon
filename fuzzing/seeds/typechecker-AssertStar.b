module AssertStar

interface {}

function test()
{
    assert *;  // Typechecker error.
}
