module Main

interface {}

function test()
{
    match 1 {
        // Error, int literal too low for i64 (Reported by parser)
        case -9223372036854775809 => true;
    }
}
