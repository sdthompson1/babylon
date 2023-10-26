module StringCopy

interface {
    function main();
}

import Test;

const hello_string: u8[] = "Hello world!\n";

const strings_in_tuple = {"Test_String_1\n", "Test_String_2\n"};

function copy_string(ref to: u8[], from: u8[])
    requires sizeof(to) == sizeof(from);
{
    var i: u64 = u64(0);
    while i < sizeof(to)
        invariant sizeof(to) == sizeof(from);
        decreases ~i;
    {
        to[i] = from[i];
        i = i + u64(1);
    }
}

function main()
{
    var tmp: u8[];
    resize_array<u8>(tmp, sizeof(hello_string));
    
    copy_string(tmp, hello_string);

    Test.print_string(tmp);

    resize_array<u8>(tmp, 0);

    Test.print_string(strings_in_tuple.0);
    Test.print_string(strings_in_tuple.1);
}
