module RecursiveTyapp
interface {}

// Regression test for crash involving recursive function and type-application.

function illegal_rec<a>()
{
    illegal_rec<a>();
}

function test5()
{
    illegal_rec<i32>(1);    // Ignored error
}
