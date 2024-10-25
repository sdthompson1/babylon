module StringCopy

interface {
    function main();
}

import Test;

const hello_string: u8[] = "Hello world!\n";  // note cast: u8[14] to u8[]

// unfortunately casting tuples of string literals does not currently work,
// so the below must be written const strings_in_tuple = ...
// rather than const strings_in_tuple: {u8[], u8[]} = ...
// TODO: might want to fix this some day
const strings_in_tuple = {"Test_String_1\n", "Test_String_2\n"};

function copy_string(ref to: u8[], from: u8[])
    requires sizeof(to) == sizeof(from);
    ensures to == from;
{
    var i: u64 = u64(0);
    while i < sizeof(to)
        invariant sizeof(to) == sizeof(from);
        invariant i <= sizeof(to);
        invariant forall (j: u64) j < i ==> to[j] == from[j];
        decreases ~i;
    {
        to[i] = from[i];
        i = i + u64(1);
    }
}

function main()
{
    var tmp: u8[*];
    alloc_array<u8>(tmp, sizeof(hello_string));
    
    copy_string(tmp, hello_string);

    Test.print_string(tmp);

    free_array<u8>(tmp);

    Test.print_string(strings_in_tuple.0);
    Test.print_string(strings_in_tuple.1);
}
