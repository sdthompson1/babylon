module Main

interface {
    // This is one below the i64 min.
    // Here, we have a minus sign followed by a valid (u64) int literal.
    // The parser tries to combine these into a single (i64) int literal,
    // but fails because the result is out of range.
    // Hence we get the "int literal too big" error (but from the parser,
    // not the lexer, in this case).
    const i64_below_min: i64 = -9223372036854775809;
}
