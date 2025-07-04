module IntLiteralTooBig

interface {
    // This is the max possible u64
    const valid:   u64 = 18446744073709551615;

    // This is one higher than the max possible u64 - Error detected by lexer
    const too_big: u64 = 18446744073709551616;

    // This is way too big - Error detected by lexer
    const silly: u64 = 999999999999999999999999999999999999999999999999999999999999999999999999999999999999999;
}
