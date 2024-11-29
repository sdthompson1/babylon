module Literals

interface {
    function main();
}

import Test;

// Hex and character literals

function main()
{
    Test.print_i32(0x1234);
    Test.print_i32(0x12345678);
    Test.print_i64(0xabcdABCD);
    Test.print_u64(0xffffffffffffffff);

    Test.print_u8(' ');
    Test.print_u8('!');
    Test.print_u8('"');
    Test.print_u8('\"');
    Test.print_u8('#');
    Test.print_u8('$');
    Test.print_u8('%');
    Test.print_u8('&');
    Test.print_u8('\'');
    Test.print_u8('(');
    Test.print_u8(')');
    Test.print_u8('*');
    Test.print_u8('+');
    Test.print_u8(',');
    Test.print_u8('-');
    Test.print_u8('.');
    Test.print_u8('/');
    Test.print_u8('0');
    Test.print_u8('1');
    Test.print_u8('9');
    Test.print_u8(':');
    Test.print_u8(';');
    Test.print_u8('<');
    Test.print_u8('=');
    Test.print_u8('>');
    Test.print_u8('?');
    Test.print_u8('@');
    Test.print_u8('A');
    Test.print_u8('B');
    Test.print_u8('Z');
    Test.print_u8('\x00');
    Test.print_u8('\x7F');
    Test.print_u8('\n');
    Test.print_u8('\r');
    Test.print_u8('\\');
}
