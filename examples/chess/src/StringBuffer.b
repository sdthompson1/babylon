// This module provides a way of composing strings into a pre-allocated
// buffer of a fixed length.

module StringBuffer

import CString;
import Maybe;
import MemAlloc;

interface {

    type StringBuffer = {buf: u8[], pos: u64};

    function resize_string_buffer(ref mem: Mem,
                                  ref sb: StringBuffer,
                                  capacity: u64): bool
        ensures !return ==> sb == old(sb);
        ensures return ==> sizeof(sb.buf) == capacity;
        ensures return ==> sb.pos == u64(0);
        ensures capacity == u64(0) ==> return;

    function free_string_buffer(ref mem: Mem,
                                ref sb: StringBuffer)
        ensures sizeof(sb.buf) == u64(0);
    
    ghost function valid_string_buffer(sb: StringBuffer): bool
    {
        return sizeof(sb.buf) > u64(0) && sb.pos <= sizeof(sb.buf);
    }

    // Append a string, truncating if there is not enough space
    function append_string(ref sb: StringBuffer, str: u8[])
        requires valid_string_buffer(sb);
        ensures valid_string_buffer(sb);

    // Same as append_string but stops at the first zero byte in 'str'
    function append_c_string(ref sb: StringBuffer, str: u8[])
        requires valid_string_buffer(sb);
        requires valid_c_string(str);
        ensures valid_string_buffer(sb);

    // Append "\0", removing the existing final character if necessary
    function null_terminate(ref sb: StringBuffer)
        requires valid_string_buffer(sb);
        ensures valid_string_buffer(sb);
        ensures valid_c_string(sb.buf);

}

function resize_string_buffer(ref mem: Mem,
                              ref sb: StringBuffer,
                              capacity: u64): bool
    ensures !return ==> sb == old(sb);
    ensures return ==> sizeof(sb.buf) == capacity;
    ensures return ==> sb.pos == u64(0);
    ensures capacity == u64(0) ==> return;
{
    var alloc_result = resize_array<u8>(mem, sb.buf, capacity);
    if alloc_result {
        sb.pos = u64(0);
    }
    return alloc_result;
}

function free_string_buffer(ref mem: Mem,
                            ref sb: StringBuffer)
    ensures sizeof(sb.buf) == u64(0);
{
    var alloc_result = resize_array<u8>(mem, sb.buf, 0);
    assert alloc_result;
}

function append_string(ref sb: StringBuffer,
                       str: u8[])
    requires valid_string_buffer(sb);
    ensures valid_string_buffer(sb);
{
    var i: u64 = 0;
    while i < sizeof(str) && sb.pos < sizeof(sb.buf)
        invariant valid_string_buffer(sb);
        decreases ~i;
    {
        sb.buf[sb.pos] = str[i];
        i = i + u64(1);
        sb.pos = sb.pos + u64(1);
    }
}

function append_c_string(ref sb: StringBuffer,
                         str: u8[])
    requires valid_string_buffer(sb);
    requires valid_c_string(str);
    ensures valid_string_buffer(sb);
{
    var i: u64 = 0;
    while i < sizeof(str) && str[i] != 0 && sb.pos < sizeof(sb.buf)
        invariant valid_string_buffer(sb);
        decreases ~i;
    {
        sb.buf[sb.pos] = str[i];
        i = i + u64(1);
        sb.pos = sb.pos + u64(1);
    }
}

function null_terminate(ref sb: StringBuffer)
    requires valid_string_buffer(sb);
    ensures valid_string_buffer(sb);
    ensures valid_c_string(sb.buf);    
{
    if sb.pos < sizeof(sb.buf) {
        sb.buf[sb.pos] = 0;
        sb.pos = sb.pos + u64(1);
    } else {
        assert sb.pos == sizeof(sb.buf);
        sb.buf[sizeof(sb.buf) - u64(1)] = 0;
    }
}
