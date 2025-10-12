module Main

interface {}

function test()
{
    match 1 {
        // Error, int literal too big (Reported by lexer)
        case 123456789012345678901234567890 => true
    }
}
