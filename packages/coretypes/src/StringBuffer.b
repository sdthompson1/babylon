// This module provides a way of composing strings into an allocated
// u8 array of a known length.

module StringBuffer

import Array;
import Maybe;
import String;

interface {

    type StringBuffer = {buf: u8[*], pos: u64};

    impure function alloc_string_buffer(ref sb: StringBuffer,
                                        capacity: u64): bool
        requires sizeof(sb.buf) == 0;
        ensures !return ==> sb == old(sb);
        ensures return ==> sizeof(sb.buf) == capacity;
        ensures return ==> sb.pos == 0;
        ensures capacity == 0 ==> return;

    function free_string_buffer(ref sb: StringBuffer)
        ensures sizeof(sb.buf) == 0;
    
    ghost function valid_string_buffer(sb: StringBuffer): bool
    {
        return sizeof(sb.buf) > 0 && sb.pos <= sizeof(sb.buf);
    }

    // Append a string, truncating if there is not enough space
    function append_string(ref sb: StringBuffer, str: u8[])
        requires valid_string_buffer(sb);
        requires valid_string(str);
        ensures valid_string_buffer(sb);

    // Append null byte, removing the existing final character if necessary
    function null_terminate(ref sb: StringBuffer)
        requires valid_string_buffer(sb);
        ensures valid_string_buffer(sb);
        ensures valid_string(sb.buf);

}

impure function alloc_string_buffer(ref sb: StringBuffer,
                                    capacity: u64): bool
    requires sizeof(sb.buf) == 0;
    ensures !return ==> sb == old(sb);
    ensures return ==> sizeof(sb.buf) == capacity;
    ensures return ==> sb.pos == 0;
    ensures capacity == 0 ==> return;
{
    if capacity == 0 {
        sb.pos = 0;
        return true;
    }
    var alloc_result = alloc_array(sb.buf, capacity);
    if alloc_result {
        sb.pos = 0;
    }
    return alloc_result;
}

function free_string_buffer(ref sb: StringBuffer)
    ensures sizeof(sb.buf) == 0;
{
    free_array(sb.buf);
}

function append_string(ref sb: StringBuffer,
                       str: u8[])
    requires valid_string_buffer(sb);
    requires valid_string(str);
    ensures valid_string_buffer(sb);
{
    var i: u64 = 0;
    while i < sizeof(str) && str[i] != 0 && sb.pos < sizeof(sb.buf)
        invariant valid_string_buffer(sb);
        decreases ~i;
    {
        sb.buf[sb.pos] = str[i];
        i = i + 1;
        sb.pos = sb.pos + 1;
    }
}

function null_terminate(ref sb: StringBuffer)
    requires valid_string_buffer(sb);
    ensures valid_string_buffer(sb);
    ensures valid_string(sb.buf);    
{
    if sb.pos < sizeof(sb.buf) {
        sb.buf[sb.pos] = 0;
        sb.pos = sb.pos + 1;
    } else {
        assert sb.pos == sizeof(sb.buf);
        sb.buf[sizeof(sb.buf) - 1] = 0;
    }
}
