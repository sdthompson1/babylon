module HexLiteralInvalid

interface {}

const foo: u64 = 00x12;  // Illegal, should be 0x12
