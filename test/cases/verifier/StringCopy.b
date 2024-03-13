module StringCopy

interface {
    function main();
}

import Test;

const hello_string: u8[14] = "Hello world!\n";
const strings_in_tuple = {"Test_String_1\n", "Test_String_2\n"};

function copy_string(ref to: u8[], from: u8[])
    requires sizeof(to) == sizeof(from);
    ensures to == from;
{
    var i: u64 = u64(0);
    while i < sizeof(to)
        invariant sizeof(to) == sizeof(from);
        invariant i <= sizeof(from);
        invariant (forall (j:u64) j < i ==> to[j] == from[j]);
        decreases ~i;
    {
        to[i] = from[i];
        i = i + u64(1);
    }
}

function main()
{
    var tmp: u8[*];
    resize_array<u8>(tmp, sizeof(hello_string));

    copy_string(tmp, hello_string);
    assert tmp[5] == 32;   // ascii space = 32

    resize_array<u8>(tmp, 0);

    assert strings_in_tuple.0[0] == strings_in_tuple.1[0];
    assert sizeof(strings_in_tuple.0) == sizeof(strings_in_tuple.1);
}

function dummy()
{
    assert false;
}
