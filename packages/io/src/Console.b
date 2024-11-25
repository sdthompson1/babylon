module Console

// Some functions for printing to stdout.

// These operations could be done using the File module
// (by using open_stdout and write_str_ln, for example)
// but this module is more convenient for simple printing operations.

import String;

interface {
    // Print a string to stdout.
    // Note: Doesn't have to be 'impure' because doesn't return anything.
    extern function print(str: u8[])
            = "Console_print";
        requires valid_string(str);

    // Print a string to stdout, then print a newline.
    extern function println(str: u8[])
            = "Console_println";
        requires valid_string(str);

    // Print various integer types to stdout, in decimal format.
    function print_i64(num: i64);
    function print_i32(num: i32) { print_i64(num); }
    function print_i16(num: i16) { print_i64(num); }
    function print_i8(num: i8) { print_i64(num); }
    function print_u64(num: u64);
    function print_u32(num: u32) { print_u64(num); }
    function print_u16(num: u16) { print_u64(num); }
    function print_u8(num: u8) { print_u64(num); }
}

function print_i64(num: i64)
{
    var buf: u8[21];
    i64_to_string(num, buf);
    print(buf);
}

function print_u64(num: u64)
{
    var buf: u8[21];
    u64_to_string(num, buf);
    print(buf);
}
